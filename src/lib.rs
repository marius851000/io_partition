//! This rust crate allow to take a part of an object that implement ``Read`` + ``Seek`` (typically a file), by specifying it's offset and lenght. It can also build similar item with an Arc<Mutex<File>>, ensuring coherency of the pointer in the file, allowing to access the same file concurrently (althougth it isn't optimized for speed, as it have to unlock the Mutex and seek to the good position).
//!
//! # Examples
//! ```
//! use std::io::{Cursor, Read};
//! use io_partition::Partition;
//! let file = Cursor::new(&[0, 2, 4, 6, 8, 10, 12]);
//!
//! let mut sub_file = Partition::new(file, 2, 3).unwrap();
//! let mut buffer = [0, 0, 0, 0, 0];
//! assert_eq!(sub_file.read(&mut buffer).unwrap(), 3);
//! assert_eq!(buffer, [4, 6, 8, 0, 0]);
//! ```
//TODO: impl stream_len when seek_convenience is stabilized

use std::io;
use std::io::{Cursor, Read, Seek, SeekFrom, Write};
use std::sync::{Arc, Mutex};

const ERROR_MESSAGE_SEEK_PRE_START: &str = "can't seek before the beggining of the partition";
const ERROR_MESSAGE_OVERFLOW_POSITION_UNSIGNED: &str = "position cant be more than 2^64.";
const ERROR_MESSAGE_OVERFLOW_POSITION_SIGNED: &str = "position cant be more than 2^63.";
const ERROR_MESSAGE_START_LENGHT_OVERFLOW: &str = "the sum of the input start + lenght is superior to the maximum representatble value in a 64 bit number.";

fn partition_read<T: Read + Seek>(
    buf: &mut [u8],
    file: &mut T,
    _start: u64,
    end: u64,
    mut pointer: u64,
    seek_is_correct: bool,
) -> (u64, io::Result<usize>) {
    if !seek_is_correct {
        match file.seek(SeekFrom::Start(pointer)) {
            Ok(_) => (),
            Err(err) => return (pointer, Err(err)),
        }
    }
    let end_byte_absolute = match pointer.checked_add(buf.len() as u64) {
        Some(value) => value,
        None => {
            return (
                pointer,
                Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    ERROR_MESSAGE_OVERFLOW_POSITION_UNSIGNED,
                )),
            )
        }
    };
    if end_byte_absolute >= end {
        if end < pointer {
            return (pointer, Ok(0));
        };
        let loop_total_nb = end - pointer;
        let mut buffer1 = [0];

        for loop_nb in 0..loop_total_nb {
            match file.read_exact(&mut buffer1) {
                Ok(()) => (),
                Err(err) => {
                    let _ = file.seek(SeekFrom::Start(pointer));
                    return (pointer, Err(err));
                }
            }
            pointer += 1;
            buf[loop_nb as usize] = buffer1[0];
        }
        (pointer, Ok(loop_total_nb as usize))
    } else {
        match file.read(buf) {
            Ok(value) => (pointer + value as u64, Ok(value)),
            Err(err) => (pointer, Err(err)),
        }
    }
}

fn partition_seek<T: Read + Seek>(
    file: &mut T,
    start: u64,
    end: u64,
    pointer: u64,
    target: SeekFrom,
) -> (u64, io::Result<u64>) {
    let new_real_pos: u64 = match target {
        SeekFrom::Start(nb) => match start.checked_add(nb) {
            Some(position) => position,
            None => {
                return (
                    pointer,
                    Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        ERROR_MESSAGE_OVERFLOW_POSITION_UNSIGNED,
                    )),
                )
            }
        },
        SeekFrom::End(nb) => {
            let result_i64 = match (end as i64).checked_add(nb) {
                Some(position) => position,
                None => {
                    return (
                        pointer,
                        Err(io::Error::new(
                            io::ErrorKind::InvalidInput,
                            ERROR_MESSAGE_OVERFLOW_POSITION_SIGNED,
                        )),
                    )
                }
            };
            if result_i64 < start as i64 {
                return (
                    pointer,
                    Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        ERROR_MESSAGE_SEEK_PRE_START,
                    )),
                );
            };
            result_i64 as u64
        }
        SeekFrom::Current(nb) => {
            let result_i64 = match (pointer as i64).checked_add(nb) {
                Some(position) => position,
                None => {
                    return (
                        pointer,
                        Err(io::Error::new(
                            io::ErrorKind::InvalidInput,
                            ERROR_MESSAGE_OVERFLOW_POSITION_SIGNED,
                        )),
                    )
                }
            };
            if result_i64 < start as i64 {
                return (
                    pointer,
                    Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        ERROR_MESSAGE_SEEK_PRE_START,
                    )),
                );
            };
            result_i64 as u64
        }
    };
    if new_real_pos < start {
        return (
            pointer,
            Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                ERROR_MESSAGE_SEEK_PRE_START,
            )),
        );
    };
    // do not block seeking post-partition, as it will be caught by read
    match file.seek(SeekFrom::Start(new_real_pos as u64)) {
        Ok(_) => (),
        Err(err) => return (pointer, Err(err)),
    };
    (new_real_pos, Ok(new_real_pos - start))
}

/// A ``Partition`` allow you to refer to a part of the file. It consume the input file.
///
/// The input offset is the first byte that will be accessible. The user of the ``Partition`` won't be able to seek before it, and it will be considered the offset 0 of the ``Partition``
/// The input lenght is the number of byte that can be read with this ``Partition``. The last readable byte from the input file is input_offset + input_len
///
/// # Examples
/// ```
/// use std::io::{Cursor, Read, Seek, SeekFrom};
/// use io_partition::Partition;
///
/// let some_value = (0..100).collect::<Vec<u8>>();
/// let input_file = Cursor::new(&some_value); //0, 1, 2, 3 ... 99
///
/// let mut partition = Partition::new(input_file, 10, 20).unwrap();
///
/// let mut buffer = [0];
/// partition.read_exact(&mut buffer).unwrap();
/// assert_eq!(buffer, [10]);
/// partition.read_exact(&mut buffer).unwrap();
/// assert_eq!(buffer, [11]);
///
/// assert!(partition.seek(SeekFrom::Current(-10)).is_err());
/// partition.seek(SeekFrom::End(-1)).unwrap();
/// partition.read_exact(&mut buffer).unwrap();
/// assert_eq!(buffer, [29]);
///
/// partition.seek(SeekFrom::End(-3));
/// let mut buffer_large = [0; 6];
/// assert_eq!(partition.read(&mut buffer_large).unwrap(), 3);
/// assert_eq!(buffer_large, [27, 28, 29, 0, 0, 0]);
/// ```
#[derive(Debug)]
pub struct Partition<T: Read + Seek> {
    file: T,
    /// The offset of the first byte that should be included
    start: u64,
    pointer: u64,
    /// The offset of the first byte that should be NOT included
    end: u64,
}

impl<T: Read + Seek> Partition<T> {
    /// Create new ``Partition``, with the specified input file, start and lenght
    pub fn new(file: T, start: u64, lenght: u64) -> io::Result<Partition<T>> {
        let mut result = Partition {
            file,
            start,
            pointer: start,
            end: start.checked_add(lenght).ok_or(io::Error::new(io::ErrorKind::InvalidInput, ERROR_MESSAGE_START_LENGHT_OVERFLOW))?,
        };
        result.seek(SeekFrom::Start(0))?;
        Ok(result)
    }
}

impl<T: Read + Seek> Read for Partition<T> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let (new_pointer_pos, result) = partition_read(
            buf,
            &mut self.file,
            self.start,
            self.end,
            self.pointer,
            true,
        );
        self.pointer = new_pointer_pos;
        result
    }
}

impl<T: Seek + Read> Seek for Partition<T> {
    fn seek(&mut self, pos: SeekFrom) -> io::Result<u64> {
        let (new_pointer_pos, result) =
            partition_seek(&mut self.file, self.start, self.end, self.pointer, pos);
        self.pointer = new_pointer_pos;
        result
    }
}

impl<T: Read + Seek> Write for Partition<T> {
    /// Do not use this write function. It will panic. It is just here because some library require this to have the ``Write`` trait to make this work with this (rust_vfs)
    fn write(&mut self, _: &[u8]) -> io::Result<usize> {
        Err(io::Error::from(io::ErrorKind::PermissionDenied))
    }

    /// Always suceed. It is useless to call it
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

/// A ``PartitionMutex`` allow you to refer to a part of the file. It consume the input file.
///
/// As the input file is an ``Arc<Mutex<_>>``, multiple ``PartitionMutex`` can be created by file, and ``PartitionMutex`` can be cloned.
///
/// The input offset is the first byte that will be accessible. The user of the ``PartitionMutex`` won't be able to seek before it, and it will be considered the offset 0 of the ``PartitionMutex``
/// The input lenght is the number of byte that can be read with this ``PartitionMutex``. The last readable byte from the input file is input_offset + input_len
///
/// # Examples
/// ```compile_fail
/// use std::io::{Cursor, Read, Seek, SeekFrom};
/// use io_partition::PartitionMutex;
/// use std::sync::{Mutex, Arc};
/// use std::thread;
///
/// let some_value = (0..100).collect::<Vec<u8>>();
/// let some_file = Arc::new(Mutex::new(Cursor::new(&some_value))); // does not compile due to some_value not being owned by Cursor. Work with everything with a 'static lifetime (including ``std::file::File``).
///
/// let mut first_partition = PartitionMutex::new(some_file.clone(), 10, 20).unwrap();
/// let mut second_partition = PartitionMutex::new(some_file.clone(), 40, 30).unwrap();
///
/// let mut buf = [0];
///
/// first_partition.seek(SeekFrom::Start(10)).unwrap();
/// second_partition.seek(SeekFrom::Start(5)).unwrap();
/// first_partition.read_exact(&mut buf).unwrap();
/// assert_eq!(buf, [20]);
/// second_partition.read_exact(&mut buf).unwrap();
/// assert_eq!(buf, [45]);
///
/// second_partition.seek(SeekFrom::Start(5)).unwrap();
/// let mut second_clone = second_partition.clone();
/// let handle = thread::spawn(move || {
///     second_clone.seek(SeekFrom::Current(2)).unwrap();
///     let mut buf = [0];
///     second_clone.read_exact(&mut buf).unwrap();
///     buf[0]
/// });
///
/// second_partition.seek(SeekFrom::End(0)).unwrap();
/// second_partition.read_exact(&mut buf).unwrap();
///
/// assert_eq!(handle.join().unwrap(), 47);
/// assert_eq!(buf[0], 70);
/// ```
#[derive(Debug, Clone)]
pub struct PartitionMutex<T: Read + Seek> {
    file: Arc<Mutex<T>>,
    start: u64,
    pointer: u64,
    end: u64,
}

impl<T: Read + Seek> PartitionMutex<T> {
    /// Create new ``PartitionMutex``, with the specified input file, start and lenght
    pub fn new(file: Arc<Mutex<T>>, start: u64, lenght: u64) -> io::Result<PartitionMutex<T>> {
        let mut result = PartitionMutex {
            file,
            start,
            pointer: start,
            end:start.checked_add(lenght).ok_or(io::Error::new(io::ErrorKind::InvalidInput, ERROR_MESSAGE_START_LENGHT_OVERFLOW))?,
        };
        result.seek(SeekFrom::Start(0))?;
        Ok(result)
    }
}

impl<T: Read + Seek> Read for PartitionMutex<T> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let mut file = match self.file.lock() {
            Ok(value) => value,
            Err(_) => {
                return Err(io::Error::new(
                    io::ErrorKind::Other,
                    "the file mutex is poisoned",
                ))
            }
        };
        let (new_pointer_pos, result) =
            partition_read(buf, &mut *file, self.start, self.end, self.pointer, false);
        self.pointer = new_pointer_pos;
        result
    }
}

impl<T: Read + Seek> Seek for PartitionMutex<T> {
    fn seek(&mut self, target: SeekFrom) -> io::Result<u64> {
        let mut file = match self.file.lock() {
            Ok(value) => value,
            Err(_) => {
                return Err(io::Error::new(
                    io::ErrorKind::Other,
                    "the fie mutex is poisoned",
                ))
            }
        };
        let (new_pointer_pos, result) =
            partition_seek(&mut *file, self.start, self.end, self.pointer, target);
        self.pointer = new_pointer_pos;
        result
    }
}

impl<T: Read + Seek> Write for PartitionMutex<T> {
    /// Do not use this write function. It will panic. It is just here because some library require this to have the ``Write`` trait to make this work with this (rust_vfs)
    fn write(&mut self, _: &[u8]) -> io::Result<usize> {
        Err(io::Error::from(io::ErrorKind::PermissionDenied))
    }

    /// Always suceed. It is useless to call it
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

/// Clone a part of a file into a Vec
pub fn clone_into_vec<T: Read + Seek>(
    file: &mut T,
    start: u64,
    length: u64,
) -> Result<Vec<u8>, io::Error> {
    let mut buffer = [0];
    file.seek(SeekFrom::Start(start))?;
    let mut output_buffer = Vec::new();
    for _ in 0..length {
        file.read_exact(&mut buffer)?;
        output_buffer.push(buffer[0]);
    }
    Ok(output_buffer)
}

/// Clone a part of a file
pub fn partition_clone<T: Read + Seek>(
    file: &mut T,
    start: u64,
    length: u64,
) -> Result<Cursor<Vec<u8>>, io::Error> {
    Ok(Cursor::new(clone_into_vec(file, start, length)?))
}
