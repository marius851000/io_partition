#![no_main]
#[macro_use]
extern crate libfuzzer_sys;
extern crate arbitrary;
extern crate io_partition;
use arbitrary::{Arbitrary, Unstructured, Result};
use std::io::Cursor;
use std::io::{Read, Write, Seek, SeekFrom};
use std::sync::{Arc, Mutex};

#[derive(Debug, Clone)]
pub struct ArbitraryPartition {
    start: u64,
    lenght: u64,
    data: Vec<u8>,
    action: Vec<ReadWriteAction>
}

impl Arbitrary for ArbitraryPartition {
    fn arbitrary(u: &mut Unstructured<'_>) -> Result<Self> {
        let start = u64::arbitrary(u)?;
        let lenght = u64::arbitrary(u)?;
        let data = Vec::<u8>::arbitrary(u)?;
        let action = Vec::<ReadWriteAction>::arbitrary(u)?;
        Ok(ArbitraryPartition {
            start,
            lenght,
            data,
            action
        })
    }
}

#[derive(Debug, Clone)]
pub enum ReadWriteAction {
    Read(usize),
    Seek(SeekFrom),
    Write(usize),
}

impl Arbitrary for ReadWriteAction {
    fn arbitrary(u: &mut Unstructured<'_>) -> Result<Self> {
        Ok(match u32::arbitrary(u)? % 3 {
            0 => ReadWriteAction::Read(usize::arbitrary(u)?),
            1 => ReadWriteAction::Seek(match u32::arbitrary(u)? % 3 {
                0 => SeekFrom::Start(u64::arbitrary(u)?),
                1 => SeekFrom::Current(i64::arbitrary(u)?),
                2 => SeekFrom::End(i64::arbitrary(u)?),
                _ => panic!(),
            }),
            2 => ReadWriteAction::Write(usize::arbitrary(u)?),
            _ => panic!(),
        })
    }
}

fuzz_target!(|data: [ArbitraryPartition; 10]| {
    for data in data.iter() {
        let input = Cursor::new(data.data.clone());
        let partition = io_partition::PartitionMutex::new(Arc::new(Mutex::new(input)), data.start, data.lenght);
        match partition {
            Ok(mut partition) => {
                for action in data.action.clone() {
                    match action {
                        ReadWriteAction::Read(lenght) => {
                            if lenght > 10000 {
                                continue;
                            };
                            let mut buffer = vec![0; lenght];
                            let _ = partition.read(&mut buffer);
                        }
                        ReadWriteAction::Seek(value) => {
                            let _ = partition.seek(value);
                        }
                        ReadWriteAction::Write(lenght) => {
                            if lenght > 10000 {
                                continue;
                            };
                            let mut buffer = vec![0; lenght];
                            let _ = partition.write(&mut buffer);
                        }
                    }
                }
            }
            Err(_) => (),
        };
    }
});
