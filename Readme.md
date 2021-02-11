# io_partition
This rust crate allow to take a part of an object that implement Read + Seek (typically a file), by specifing it's offset and lenght. It can also build similar item with an Arc<Mutex<File>>, ensuring coherency of the pointer in the file, allowing to access the same file concurrently (althougth it isn't optimized for speed, as it have to unlock the Mutex and seek to the good position).

This mutex can however be locked for single-threader access, allowing near-native performance.