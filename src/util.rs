//! Useful utilities.

use std::fmt;
use std::io::{self, Read, BufRead};
use memchr::Memchr;

/// A line-and-column position within a file.
///
/// Note that, when formatted using `Display`, line and column numbers will be
/// adjusted to be one-based, rather than the zero-based used internally.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Position {
    /// Zero-based line number.
    pub line: u64,

    /// Zero-based column number.
    pub column: u64,
}

impl Position {
    /// Create a new `Position` from zero-based numbers.
    pub fn new_zero(line: u64, column: u64) -> Self {
        Position { line, column }
    }

    /// Create a new `Position` from one-based numbers.
    pub fn new_one(line: u64, column: u64) -> Self {
        Position {
            line: line.saturating_sub(1),
            column: column.saturating_sub(1),
        }
    }
}

impl fmt::Display for Position {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "{}:{}", self.line + 1, self.column + 1)
    }
}

/// This type wraps around a `Read` or `BufRead` type and tracks where lines begin.
///
/// This can be used to map byte positions within the observed stream to line-and-column `Position` values.
pub struct PositionRead<R> {
    reader: R,
    track: PositionTrack,
    buf_scanned: usize,
}

impl<R> PositionRead<R> {
    /// Create a `PositionRead`.
    ///
    /// This assumes the underlying reader is currently at byte position 0.
    pub fn new(reader: R) -> Self {
        Self::new_with_offset(reader, 0)
    }

    /// Create a `PositionRead` at a non-zero offset.
    ///
    /// This may be useful if you are only doing line tracking on a subset of a source stream.
    ///
    /// **Note**: non-public because it's too easy for users to shoot themselves in the foot with it.  If they're using this with a `Reader`, they *absolutely must not* set the `offset` to anything other than 0, even if they *are* parsing a subset.
    fn new_with_offset(reader: R, offset: u64) -> Self {
        PositionRead {
            reader,
            track: PositionTrack {
                current_offset: offset,
                line_offsets: vec![offset],
            },
            buf_scanned: 0,
        }
    }

    /// Returns the current byte offset of the line tracker.
    #[inline]
    pub fn current_offset(&self) -> u64 {
        self.track.current_offset
    }

    /// Returns a slice of line offsets.
    ///
    /// Each element of the slice is the byte offset at which the line begins.  The first element will contain the offset with which the `PositionRead` was created.
    #[inline]
    pub fn line_offsets(&self) -> &[u64] {
        &self.track.line_offsets
    }

    /// Provides immutable access to the underlying stream.
    ///
    /// **Note**: You *should not* do anything which could change the state of the stream.  If you do so, line tracking may become inaccurate.
    #[inline]
    pub fn inner(&self) -> &R {
        &self.reader
    }

    /// Consumes the `PositionRead` and returns the underlying stream value.
    #[inline]
    pub fn into_inner(self) -> R {
        self.reader
    }

    /// Breaks the `PositionRead` into its constituent, owned parts.
    #[inline]
    pub fn explode(self) -> (R, Vec<u64>) {
        (self.reader, self.track.line_offsets)
    }
}

impl<R: BufRead> BufRead for PositionRead<R> {
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        let buf = self.reader.fill_buf()?;

        /*
        We want to immediately scan this buffer, since we may be asked to resolve a byte offset within this buffer *before* `consume` is called.
        
        However, it's possible for someone to call this multiple times without consuming anything, so we don't want to process any byte more than once.

        `buf_scanned` holds the number of bytes we've seen come out of the underlying reader, but which *have not* yet been consumed by a call to either `consume` or `Read::read`.

        In other words, we have to ignore the first `buf_scanned` bytes, process the rest, and then increase it by the number of bytes we *did* process.

        At the limit, `buf_scanned` shouldn't exceed the size of the underlying buffer, so we shouldn't need to worry about overflows.
        */
        {
            let unprocessed_buf = &buf[self.buf_scanned..];
            self.track.scan_buffer(unprocessed_buf);
            self.buf_scanned += unprocessed_buf.len();
        }

        Ok(buf)
    }

    fn consume(&mut self, amt: usize) {
        self.reader.consume(amt);

        /*
        To quote the `BufRead` docs:

        > The `amt` must be `<=` the number of bytes in the buffer returned by `fill_buf`.

        We will make it a hard failure to violate this, as it would imply consuming bytes we've never seen, and cannot scan.
        */
        if amt > self.buf_scanned {
            panic!("cannot call PositionRead::consume on more bytes than have been returned by fill_buf");
        }
        self.buf_scanned -= amt;
    }
}

impl<R: Read> Read for PositionRead<R> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        // Because we don't know exactly how the underlying buffer works, we're going to just *forbid* mixing `fill_buf` and `read`.
        if self.buf_scanned != 0 {
            panic!("cannot mix using Read and BufRead on a PositionRead");
        }

        match self.reader.read(buf) {
            Ok(0) => Ok(0),
            Ok(bytes) => {
                self.track.scan_buffer(&buf[..bytes]);
                Ok(bytes)
            },
            Err(err) => Err(err),
        }
    }
}

/// Trait for types which can resolve byte offsets to positions.
///
/// This trait is provided for users who wish to use a different position tracking type.
pub trait PositionResolve {
    /// The associated error type for when resolution fails.
    type ResolveError;

    /// Resolves a byte offset to a line and column position.
    ///
    /// Returns `Err` if the offset is outside the resolvable range.
    fn try_resolve(&self, offset: u64) -> Result<Position, Self::ResolveError>;

    /// Resolves a byte offset to a line and column position.
    ///
    /// May panics if the offset given is outside the resolvable range.
    fn resolve(&self, offset: u64) -> Position {
        match self.try_resolve(offset) {
            Ok(pos) => pos,
            Err(_) => panic!("could not resolve offset {:?}", offset),
        }
    }
}

/// Internal type for holding the actual line tracking information.
struct PositionTrack {
    current_offset: u64,
    line_offsets: Vec<u64>,
}

impl PositionTrack {
    /// Scans the given buffer for line terminators, and updates the tracker accordingly.
    fn scan_buffer(&mut self, buf: &[u8]) {
        for off in Memchr::new(b'\n', buf) {
            let abs_off = self.current_offset + (off as u64);
            self.line_offsets.push(abs_off);
        }
        self.current_offset += buf.len() as u64;
    }

    /// Try to resolve the given byte offset.
    fn try_resolve(&self, offset: u64) -> Result<Position, ResolveError> {
        if offset > self.current_offset {
            return Err(ResolveError::After(self.current_offset));
        }

        let idx = match self.line_offsets.binary_search(&offset) {
            Ok(idx) => {
                // An exact match.  Good to go.
                idx
            },
            Err(0) => {
                // This can happen if the user started the `PositionRead` at a non-zero offset.  In this case, we can't resolve this byte position.
                return Err(ResolveError::Before(self.line_offsets[0]))
            },
            Err(idx) => {
                /*
                Imagine we have the following data in `line_offsets`:
                
                    [ 0, 10, 35, 60, .. ]

                If we fail to find an offset of `8`, the index returned will be `1`: where to insert `8` into the existing data to maintain sorted order.  However, `8` is part of line 0, not line 1, so we subtract one.  This is also *always* safe because we can't possibly get `Err(0)` as explained above.
                */
                idx - 1
            },
        };

        // Sanity check
        debug_assert!(::std::mem::size_of::<usize>() <= ::std::mem::size_of::<u64>());
        
        let line = idx as u64;
        let column = offset - self.line_offsets[idx];
        Ok(Position { line, column })
    }
}

impl<R> PositionResolve for PositionRead<R> {
    type ResolveError = ResolveError;

    fn try_resolve(&self, offset: u64) -> Result<Position, Self::ResolveError> {
        self.track.try_resolve(offset)
    }

    fn resolve(&self, offset: u64) -> Position {
        match self.try_resolve(offset) {
            Ok(pos) => pos,
            Err(ResolveError::Before(beg)) => panic!("could not resolve offset \
                {:?}: can only resolve offsets beginning at {:?}", offset, beg),
            Err(ResolveError::After(end)) => panic!("could not resolve offset \
                {:?}: maximum observed offset is {:?}", offset, end),
        }
    }
}

/// Indicates why an attempt to resolve a byte position failed.
pub enum ResolveError {
    /// The byte position was before the earliest tracked offset.
    Before(u64),
    /// The byte position was after the latest tracked offset.
    After(u64),
}
