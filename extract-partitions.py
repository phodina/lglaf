#!/usr/bin/env python
#
# Dump partitions to file.
#
# Copyright (C) 2015 Peter Wu <peter@lekensteyn.nl>
# Copyright (C) 2017-2023 steadfasterX <steadfasterX |AT| binbash #DOT# rocks>
#
# Licensed under the MIT license <http://opensource.org/licenses/MIT>.

from contextlib import closing
import argparse, logging, os, struct
import lglaf, partitions

_logger = logging.getLogger("extract-partitions")

parser = argparse.ArgumentParser()
parser.add_argument("--cr", choices=['yes', 'no'], help="Do initial challenge response (KILO CENT/METR)")
parser.add_argument("-d", "--outdir", default=".",
        help="Output directory for disk images.")
# Do not dump partitions larger than this size
# (userdata 11728 MiB, system 2064 MiB, cache 608 MiB, cust 256 MiB)
parser.add_argument("--max-size", metavar="kbytes", type=int, default=65535,
        help="Maximum partition size to dump (in KiB) or 0 to dump all (default %(default)d)")
parser.add_argument("--debug", action='store_true', help="Enable debug messages")
parser.add_argument("--batch", action='store_true', help="Enable batch mode")
parser.add_argument("--skip-hello", action="store_true",
        help="Immediately send commands, skip HELO message")
parser.add_argument("--devtype", choices=['UFS', 'EMMC'],
        help="Force the device type (UFS or EMMC)")
parser.add_argument("--sign", metavar="LOCAL_PATH",
        help="Send sign payload for signed writing ('-' for stdin)")
parser.add_argument("partition", nargs='?',
        help="Partition number (e.g. 1 for block device mmcblk0p1)"
        " or partition name (e.g. 'recovery')")

def dump_partitions(comm, disk_fd, outdir, max_size, batch):
    diskinfo = partitions.get_partitions(comm, disk_fd)
    for part in diskinfo.gpt.partitions:
        part_offset = part.first_lba * partitions.BLOCK_SIZE
        part_size = ((part.last_lba + 1) - part.first_lba) * partitions.BLOCK_SIZE
        part_name = part.name
        part_label = "/dev/mmcblk0p%i" % part.index
        if max_size and part_size > max_size:
            if batch:
                print("#Ignoring large partition %s (%s) of size %dK" % (part_label, part_name, part_size / 1024))
            else:
                _logger.info("Ignoring large partition %s (%s) of size %dK",
                    part_label, part_name, part_size / 1024)
            continue
        out_path = os.path.join(outdir, "%s.bin" % part_name)
        try:
            current_size = os.path.getsize(out_path)
            if current_size > part_size:
                if batch:
                    print("#%s: unexpected size %dK, larger than %dK" % (out_path, current_size / 1024, part_size / 1024))
                else:
                    _logger.warn("%s: unexpected size %dK, larger than %dK",
                        out_path, current_size / 1024, part_size / 1024)
                continue
            elif current_size == part_size:
                if batch:
                    print("#Skipping already existing partition %s (%s)" % ( part_label, part_name))
                else:
                    _logger.info("Skipping partition %s (%s), already found at %s",
                        part_label, part_name, out_path)
                continue
        except OSError: pass

        if batch:
            print("#%s (%s)" % (part_label, part_name))
        else:
            _logger.info("Dumping partition %s (%s) to %s (%d bytes)",
                part_label, part_name, out_path, part_size)
   
        partitions.dump_partition(comm, disk_fd, out_path, part_offset, part_size, batch)

def main():
    args = parser.parse_args()
    logging.basicConfig(format='%(asctime)s %(name)s: %(levelname)s: %(message)s',
            level=logging.DEBUG if args.debug else logging.INFO)

    try: os.makedirs(args.outdir)
    except OSError: pass

    comm = lglaf.autodetect_device(args.cr)
    with closing(comm):
        if not args.skip_hello:
            lglaf.set_protocol(comm)
            _logger.debug("Using Protocol version: 0x%x" % comm.protocol_version)

        devtype, part_header, part_table = partitions.detect_and_open_fd(comm, args)
        dev, part_opener, filtered_ptable = partitions.list_filtered(part_table, args)
        disk_fd = partitions.laf_open_disk(comm, part_opener)
        _logger.debug("Opened fd %d for disk", disk_fd)
        dump_partitions(comm, disk_fd, args.outdir, args.max_size * 1024, args.batch)

    if args.batch:
        print("#All finished")
    else:
        _logger.info("All finished!")

if __name__ == '__main__':
    main()
