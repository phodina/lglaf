#!/usr/bin/env python3
#
# Manage a single partition (info, read, write).
#
# Copyright (C) 2015 Peter Wu <peter@lekensteyn.nl>
# Copyright (C) 2017-2023 steadfasterX <steadfasterX |AT| binbash #DOT# rocks>
#
# Licensed under the MIT license <http://opensource.org/licenses/MIT>.

from __future__ import print_function,division
from collections import OrderedDict
from contextlib import closing, contextmanager
import argparse, logging, os, io, struct, sys, time, re
import lglaf
import gpt
import zlib
import binascii
try: import usb.core, usb.util
except ImportError: pass

_logger = logging.getLogger("partitions")

def_body = b'\0'
sda_body = b'\x2f\x64\x65\x76\x2f\x62\x6c\x6f\x63\x6b\x2f\x73\x64\x61\x00\x06\xf8\x0f\x00\x00\x20\x90\x9d\x06\x42\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x07\x00\x00\x00\x20\x90\x9d\x06\x00\x00\x00\x00\xdd\x60\x1a\x10\x48\x52\x9f\x06\xd8\x4f\x9d\x06\x04\x00\x00\x00\x00\x00\x00\x00\x58\x52\x9f\x06\x00\x00\x00\x00\x0c\x00\x04\x00\x07\x00\x00\x00\x60\xea\xff\x03\xeb\x27\x00\x10\xdc\xea\xff\x03\x20\x90\x9d\x06\x64\xea\xff\x03\x41\x76\x1a\x10\x00\x00\x61\x06\x00\x00\x00\x00\x20\x90\x9d\x06\xc0\xea\xff\x03\xbe\xe4\x09\x10\x20\x90\x9d\x06\xb6\xd9\xee\xd8\x02\x00\x00\x00\xbc\x52\xa7\x06\xdb\xe4\x09\x10\x20\x90\x9d\x06\x20\xa0\x9d\x06\x20\xa0\x9d\x06\x00\x00\x00\x00\xdc\xea\xff\x03\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x0f\x00\x00\x00\x00\x00\x00\x00\xb6\xd9\xee\xd8\xfc\xea\xff\x03\xf0\x9a\x1d\x10\x02\x00\x00\x00\x10\x00\x00\x00\x08\xeb\xff\x03\x7b\x8c\x03\x10\x10\x00\x00\x00\x8a\x8c\x03\x10\x7e\xd8\xee\xd8\xba\x8c\x03\x10\x00\x61\x63\x74\x6f\x72\x79\x00\xa0\xe8\xff\x03\x9c\xec\xff\x03\x02\x00\x02\x00\xb6\x81\x00\x00\x00\x00\xb6\x01\x00\x00\x00\x00\x00\x00\x00\x00'
sdb_body = b'\x2f\x64\x65\x76\x2f\x62\x6c\x6f\x63\x6b\x2f\x73\x64\x62\x00\x06\xf9\x0f\x00\x00\x08\x60\x9d\x06\x42\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x06\x00\x00\x00\x08\x60\x9d\x06\x00\x00\x00\x00\xdd\x60\x1a\x10\x48\x52\x9f\x06\xd8\x4f\x9d\x06\x01\x00\x00\x00\x00\x00\x00\x00\x58\x52\x9f\x06\x00\x00\x00\x00\x0c\x00\x01\x00\x06\x00\x00\x00\x60\xea\xff\x03\xeb\x27\x00\x10\xdc\xea\xff\x03\x08\x60\x9d\x06\x64\xea\xff\x03\x41\x76\x1a\x10\x00\x00\x61\x06\x00\x00\x00\x00\x08\x60\x9d\x06\xc0\xea\xff\x03\xbe\xe4\x09\x10\x08\x60\x9d\x06\xb6\xd9\xee\xd8\x3f\x00\x00\x00\xbc\x52\xa7\x06\xdb\xe4\x09\x10\x08\x60\x9d\x06\x08\x70\x9d\x06\x08\x70\x9d\x06\x00\x00\x00\x00\xdc\xea\xff\x03\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x0f\x00\x00\x00\x00\x00\x00\x00\xb6\xd9\xee\xd8\xfc\xea\xff\x03\xf0\x9a\x1d\x10\x3f\x00\x00\x00\x10\x00\x00\x00\x08\xeb\xff\x03\x7b\x8c\x03\x10\x10\x00\x00\x00\x8a\x8c\x03\x10\x7e\xd8\xee\xd8\xba\x8c\x03\x10\x00\x62\x6c\x62\x61\x6b\x00\xd8\xa0\xe8\xff\x03\x9c\xec\xff\x03\x02\x00\x02\x00\xb6\x81\x00\x00\x00\x00\xb6\x01\x00\x00\x00\x00\x00\x00\x00\x00'
sdc_body = b'\x2f\x64\x65\x76\x2f\x62\x6c\x6f\x63\x6b\x2f\x73\x64\x63\x00\x06\xfb\x0f\x00\x00\x30\xb0\x9d\x06\x42\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x04\x00\x00\x00\x30\xb0\x9d\x06\x00\x00\x00\x00\xdd\x60\x1a\x10\x48\x52\x9f\x06\xd8\x4f\x9d\x06\x06\x00\x00\x00\x00\x00\x00\x00\x58\x52\x9f\x06\x00\x00\x00\x00\x0c\x00\x06\x00\x04\x00\x00\x00\x60\xea\xff\x03\xeb\x27\x00\x10\xdc\xea\xff\x03\x30\xb0\x9d\x06\x64\xea\xff\x03\x41\x76\x1a\x10\x00\x00\x61\x06\x00\x00\x00\x00\x30\xb0\x9d\x06\xc0\xea\xff\x03\xbe\xe4\x09\x10\x30\xb0\x9d\x06\xb6\xd9\xee\xd8\x42\x00\x00\x00\xbc\x52\xa7\x06\xdb\xe4\x09\x10\x30\xb0\x9d\x06\x30\xc0\x9d\x06\x30\xc0\x9d\x06\x00\x00\x00\x00\xdc\xea\xff\x03\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x0f\x00\x00\x00\x00\x00\x00\x00\xb6\xd9\xee\xd8\xfc\xea\xff\x03\xf0\x9a\x1d\x10\x42\x00\x00\x00\x10\x00\x00\x00\x08\xeb\xff\x03\x7b\x8c\x03\x10\x10\x00\x00\x00\x8a\x8c\x03\x10\x7e\xd8\xee\xd8\xba\x8c\x03\x10\x00\x62\x6c\x32\x00\xd9\xee\xd8\xa0\xe8\xff\x03\x9c\xec\xff\x03\x02\x00\x02\x00\xb6\x81\x00\x00\x00\x00\xb6\x01\x00\x00\x00\x00\x00\x00\x00\x00'
sdd_body = b'\x2f\x64\x65\x76\x2f\x62\x6c\x6f\x63\x6b\x2f\x73\x64\x64\x00\x06\xf6\x0f\x00\x00\x08\x60\x9d\x06\x42\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x09\x00\x00\x00\x08\x60\x9d\x06\x00\x00\x00\x00\xdd\x60\x1a\x10\x48\x52\x9f\x06\xd8\x4f\x9d\x06\x01\x00\x00\x00\x00\x00\x00\x00\x58\x52\x9f\x06\x00\x00\x00\x00\x0c\x00\x01\x00\x09\x00\x00\x00\x60\xea\xff\x03\xeb\x27\x00\x10\xdc\xea\xff\x03\x08\x60\x9d\x06\x64\xea\xff\x03\x41\x76\x1a\x10\x00\x00\x61\x06\x00\x00\x00\x00\x08\x60\x9d\x06\xc0\xea\xff\x03\xbe\xe4\x09\x10\x08\x60\x9d\x06\xb6\xd9\xee\xd8\x46\x00\x00\x00\xbc\x52\xa7\x06\xdb\xe4\x09\x10\x08\x60\x9d\x06\x08\x70\x9d\x06\x08\x70\x9d\x06\x00\x00\x00\x00\xdc\xea\xff\x03\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x0f\x00\x00\x00\x00\x00\x00\x00\xb6\xd9\xee\xd8\xfc\xea\xff\x03\xf0\x9a\x1d\x10\x46\x00\x00\x00\x10\x00\x00\x00\x08\xeb\xff\x03\x7b\x8c\x03\x10\x10\x00\x00\x00\x8a\x8c\x03\x10\x7e\xd8\xee\xd8\xba\x8c\x03\x10\x00\x61\x63\x6b\x75\x70\x47\x50\x54\x00\xff\x03\x9c\xec\xff\x03\x02\x00\x02\x00\xb6\x81\x00\x00\x00\x00\xb6\x01\x00\x00\x00\x00\x00\x00\x00\x00'
sde_body = b'\x2f\x64\x65\x76\x2f\x62\x6c\x6f\x63\x6b\x2f\x73\x64\x65\x00\x06\xfb\x0f\x00\x00\x30\xb0\x9d\x06\x42\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x04\x00\x00\x00\x30\xb0\x9d\x06\x00\x00\x00\x00\xdd\x60\x1a\x10\x48\x52\x9f\x06\xd8\x4f\x9d\x06\x06\x00\x00\x00\x00\x00\x00\x00\x58\x52\x9f\x06\x00\x00\x00\x00\x0c\x00\x06\x00\x04\x00\x00\x00\x60\xea\xff\x03\xeb\x27\x00\x10\xdc\xea\xff\x03\x30\xb0\x9d\x06\x64\xea\xff\x03\x41\x76\x1a\x10\x00\x00\x61\x06\x00\x00\x00\x00\x30\xb0\x9d\x06\xc0\xea\xff\x03\xbe\xe4\x09\x10\x30\xb0\x9d\x06\xb6\xd9\xee\xd8\x48\x00\x00\x00\xbc\x52\xa7\x06\xdb\xe4\x09\x10\x30\xb0\x9d\x06\x30\xc0\x9d\x06\x30\xc0\x9d\x06\x00\x00\x00\x00\xdc\xea\xff\x03\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x0f\x00\x00\x00\x00\x00\x00\x00\xb6\xd9\xee\xd8\xfc\xea\xff\x03\xf0\x9a\x1d\x10\x48\x00\x00\x00\x10\x00\x00\x00\x08\xeb\xff\x03\x7b\x8c\x03\x10\x10\x00\x00\x00\x8a\x8c\x03\x10\x7e\xd8\xee\xd8\xba\x8c\x03\x10\x00\x6f\x6f\x74\x00\xd9\xee\xd8\xa0\xe8\xff\x03\x9c\xec\xff\x03\x02\x00\x02\x00\xb6\x81\x00\x00\x00\x00\xb6\x01\x00\x00\x00\x00\x00\x00\x00\x00\0'
sdf_body = b'\x2f\x64\x65\x76\x2f\x62\x6c\x6f\x63\x6b\x2f\x73\x64\x66\x00\x06\x18\x00\x00\x00\x00\x00\x00\x00\xd0\x23\xa2\x06\x00\x00\x00\x00\x3e\x00\x18\x00\x5e\xdf\xee\xd8\x01\x00\x00\x00\x48\x00\x9c\x06\x10\x00\x00\x00\xfe\xda\x5d\x3f\xdc\xe9\xff\x03\x30\xec\xff\x03\x41\x76\x1a\x10\x00\x00\x61\x06\x00\x00\x00\x00\x90\x63\xa3\x06\x7c\xec\xff\x03\x04\x00\x00\x00\x68\x70\x3b\x07\x82\xa6\x09\x10\x4c\x00\x00\x00\x20\x8f\x3b\x07\x80\x09\x00\x00\x48\x8f\x3b\x07\x04\x00\x00\x00\x30\x27\x00\x00\x78\xec\xff\x03\x0b\x00\x00\x00\x0f\x00\x00\x00\x6c\x00\x9c\x06\x0a\xdf\xee\xd8\x3c\xec\xff\x03\x6c\xed\xff\x03\x58\xe2\x1c\x10\xfb\xe7\x00\x00\x00\x00\x00\x00\xff\xe7\x00\x00\x00\x00\x00\x00\x90\x63\xa3\x06\x20\x3a\x20\x31\x42\x61\x63\x6b\x75\x70\x47\x50\x54\x00\x00\x08\xa0\x80\x3b\x07\x20\x10\x63\x08\x90\x70\x3b\x07\xdc\xec\xff\x03\x72\x5b\x09\x10\xa0\x80\x3b\x07\x20\x20\x63\x08\x42\x57\x09\x10\x20\x10\x63\x08\x91\x5a\x09\x10\x90\x70\x3b\x07\x21\x8f\x3b\x07\xdc\xec\xff\x03\x7c\x5b\x09\x10\x04\x00\x00\x00\xaa\xdf\xee\xd8\xf0\xec\xff\x03\x02\x00\x02\x00\xb6\x81\x00\x00\x00\x00\xb6\x01\x00\x00\x00\x00\x00\x00\x00\x00'
sdg_body = b'\x2f\x64\x65\x76\x2f\x62\x6c\x6f\x63\x6b\x2f\x73\x64\x67\x00\x06\x0b\x00\x00\x00\x00\x00\x00\x00\xd0\x23\xa2\x06\x00\x00\x00\x00\x3e\x00\x0b\x00\x5e\xdf\xee\xd8\x01\x00\x00\x00\x48\x00\x9c\x06\x10\x00\x00\x00\xfe\xda\x5d\x3f\xdc\xe9\xff\x03\x30\xec\xff\x03\x41\x76\x1a\x10\x00\x00\x61\x06\x00\x00\x00\x00\x88\x61\xa3\x06\x7c\xec\xff\x03\x05\x00\x00\x00\x68\x70\x3b\x07\x82\xa6\x09\x10\x53\x00\x00\x00\x20\x83\x3b\x07\x60\x0a\x00\x00\x48\x83\x3b\x07\x05\x00\x00\x00\xcc\x2a\x00\x00\x78\xec\xff\x03\x0b\x00\x00\x00\x0f\x00\x00\x00\x6c\x00\x9c\x06\x0a\xdf\xee\xd8\x3c\xec\xff\x03\x6c\xed\xff\x03\x58\xe2\x1c\x10\xfb\x07\x00\x00\x00\x00\x00\x00\xff\x07\x00\x00\x00\x00\x00\x00\x88\x61\xa3\x06\x20\x3a\x20\x31\x42\x61\x63\x6b\x75\x70\x47\x50\x54\x00\x00\x08\xa0\x80\x3b\x07\x20\x10\x63\x08\x90\x70\x3b\x07\xdc\xec\xff\x03\x72\x5b\x09\x10\xa0\x80\x3b\x07\x20\x20\x63\x08\x42\x57\x09\x10\x20\x10\x63\x08\x91\x5a\x09\x10\x90\x70\x3b\x07\x21\x83\x3b\x07\xdc\xec\xff\x03\x7c\x5b\x09\x10\x05\x00\x00\x00\xaa\xdf\xee\xd8\xf0\xec\xff\x03\x02\x00\x02\x00\xb6\x81\x00\x00\x00\x00\xb6\x01\x00\x00\x00\x00\x00\x00\x00\x00'

disk_opener = { 'default': def_body,
                'sda': sda_body,
                'sdb': sdb_body,
                'sdc': sdc_body,
                'sdd': sdd_body,
                'sde': sde_body,
                'sdf': sdf_body,
                'sdg': sdg_body }

def human_readable(sz):
    suffixes = ('', 'Ki', 'Mi', 'Gi', 'Ti')
    for i, suffix in enumerate(suffixes):
        if sz <= 1024**(i+1):
            break
    return '%.1f %sB' % (sz / 1024**i, suffix)

def read_uint32(data, offset):
    return struct.unpack_from('<I', data, offset)[0]

def check_block_size(comm,fd_num):
    """
    Identify the block size based on where we find the gpt header
    """
    read_offset = 0
    end_offset = GPT_LBA_LEN * BLOCK_SIZE

    _logger.debug("check_block_size, read_offset: %i, end_offset: %i, GPT_LBA_LEN: %i, BLOCK_SIZE: %i, MAX_BLOCK_SIZE: %i" %
                   (read_offset, end_offset, GPT_LBA_LEN, BLOCK_SIZE, MAX_BLOCK_SIZE))

    table_data = b''
    if hex(comm.protocol_version) >= '0x1000008':
        _logger.debug("Protocol based handling: %06x" % comm.protocol_version)
        chunksize = 17408
        data, fd_num = laf_read(comm, fd_num, read_offset // BLOCK_SIZE, chunksize, timeout=3000)
        table_data += data
        read_offset += chunksize
    else:
        while read_offset < end_offset:
            chunksize = min(end_offset - read_offset, BLOCK_SIZE * MAX_BLOCK_SIZE)
            data, fd_num = laf_read(comm, fd_num, read_offset // BLOCK_SIZE, chunksize, timeout=3000)
            table_data += data
            read_offset += chunksize

    with io.BytesIO(table_data) as table_fd:
        signature = gpt.read_gpt_header(table_fd, BLOCK_SIZE)
        if signature[0] == b'EFI PART':
            _logger.debug("GPT HEADER FOUND for block size: %s" % BLOCK_SIZE)
            return True
        else:
            _logger.debug("No GPT header found for block size: %s" % BLOCK_SIZE)
            return False

def get_partitions(comm, fd_num):
    """
    Maps partition labels (such as "recovery") to block devices (such as
    "mmcblk0p0"), sorted by the number in the block device.
    """
    read_offset = 0
    end_offset = GPT_LBA_LEN * BLOCK_SIZE

    table_data = b''
    if hex (comm.protocol_version) >= '0x1000008':
        _logger.debug("Protocol based handling: %06x" % comm.protocol_version)
        chunksize = 17408
        data, fd_num = laf_read(comm, fd_num, read_offset // BLOCK_SIZE, chunksize)
        table_data += data
        read_offset += chunksize
    else:
        while read_offset < end_offset:
            chunksize = min(end_offset - read_offset, BLOCK_SIZE * MAX_BLOCK_SIZE)
            data, fd_num = laf_read(comm, fd_num, read_offset // BLOCK_SIZE, chunksize)
            table_data += data
            read_offset += chunksize

    with io.BytesIO(table_data) as table_fd:
        info = gpt.get_disk_partitions_info(table_fd, BLOCK_SIZE)
    return info

def find_partition(diskinfo, query):
    partno = int(query) if query.isdigit() else None
    for part in diskinfo.gpt.partitions:
        if part.index == partno or part.name == query:
            return part
    raise ValueError("Partition not found: %s" % query)

def laf_open_disk(comm,opener):
    # Open whole disk in read/write mode
    open_cmd = lglaf.make_request(b'OPEN', body=opener)

    cr_needed = lglaf.chk_mode(comm.protocol_version,comm.CR_NEEDED,comm.CR_MODE)
    if cr_needed == 1:
        lglaf.challenge_response(comm, 2)
    try:
        open_header = comm.call(open_cmd)[0]
        fd_num = read_uint32(open_header, 4)
        try:
            return fd_num
        except:
            print("Error while opening a file descriptor")
    except:
        _logger.debug("Stopping here as the following open cmd is not available for this device:\n%s" % binascii.hexlify(opener))

def laf_read(comm, fd_num, offset, size, timeout=None):
    """Read size bytes at the given block offset."""
    try:
        read_cmd = lglaf.make_request(b'READ', args=[fd_num, offset, size])
    except:
        close_fd(comm,fd_num)

    for attempt in range(3):
        try:
            header, response = comm.call(read_cmd, timeout=timeout)
            break
        except usb.core.USBError as e:
            if attempt == 2:
                raise # last attempt
            if e.strerror == 'Overflow':
                _logger.debug("Overflow on READ %d %d %d", fd_num, offset, size)
                for attempt in range(3):
                    try:
                        comm.reset()
                        comm._read(-1) # clear line
                        break
                    except usb.core.USBError:
                        pass
                continue
            elif e.strerror == 'Operation timed out':
                _logger.debug("Timeout on READ %d %d %d", fd_num, offset, size)
                comm.close()
                time.sleep(3)
                comm.__init__()
                try:
                    lglaf.try_hello(comm)
                except usb.core.USBError:
                    pass
                close_cmd = lglaf.make_request(b'CLSE', args=[fd_num])
                comm.call(close_cmd)
                open_cmd = lglaf.make_request(b'OPEN', body=b'\0')
                open_header = comm.call(open_cmd)[0]
                fd_num = read_uint32(open_header, 4)
                read_cmd = lglaf.make_request(b'READ', args=[fd_num, offset, size])
                continue
            else:
                raise # rethrow

    # Ensure that response fd, offset and length are sane (match the request)
    assert read_cmd[4:4+12] == header[4:4+12], "Unexpected read response"
    assert len(response) == size
    return response, fd_num

def laf_erase(comm, fd_num, sector_start, sector_count):
    """TRIM some sectors."""
    erase_cmd = lglaf.make_request(b'ERSE',
            args=[fd_num, sector_start, sector_count])
    header, response = comm.call(erase_cmd)
    # Ensure that response fd, start and count are sane (match the request)
    assert erase_cmd[4:4+12] == header[4:4+12], "Unexpected erase response"

def laf_write(comm, fd_num, offset, write_mode, data):
    """Write size bytes at the given block offset."""
    write_cmd = lglaf.make_request(b'WRTE', args=[fd_num, offset, write_mode], body=data)
    header = comm.call(write_cmd)[0]
    # Response offset (in bytes) must match calculated offset
    calc_offset = (offset * BLOCK_SIZE) & 0xffffffff
    resp_offset = read_uint32(header, 8)
    assert write_cmd[4:4+4] == header[4:4+4], "Unexpected write response"
    assert calc_offset == resp_offset, \
            "Unexpected write response: %#x != %#x" % (calc_offset, resp_offset)

def laf_copy(comm, fd_num, src_offset, size, dst_offset):
    """This will copy blocks from one location to another on the same block device"""
    copy_cmd = lglaf.make_request(b'COPY', args=[fd_num, src_offset, size, dst_offset])
    comm.call(copy_cmd)
    # Response is unknown at this time

def laf_sign(comm, sign_payload):
    """Sends the SIGN payload for signed writing"""
    sign_cmd = lglaf.make_request(b'SIGN', body=sign_payload)
    comm.call(sign_cmd)
    #TODO: verify response

def laf_ioct(comm, fd_num, param):
    """This manipulates ioctl for a given file descriptor"""
    """The only known IOCT param is 0x1261 which enables write"""
    ioct_cmd = lglaf.make_request(b'IOCT', args=[fd_num, param])
    comm.call(ioct_cmd)

def laf_misc_write(comm, size, data):
    """This is for writting to the misc partition."""
    """You can specify an offset, but that is currently not implemented"""
    misc_offset = 0
    write_cmd = lglaf.make_request(b'MISC', args=[b'WRTE', misc_offset, size], body=data)
    #header = comm.call(write_cmd)[0]
    comm.call(write_cmd)
    # The response for MISC WRTE isn't understood yet
    #calc_offset = (offset * 4096) & 0xffffffff
    #resp_offset = read_uint32(header, 8)
    #assert write_cmd[4:4+4] == header[4:4+4], "Unexpected write response"
    #assert calc_offset == resp_offset, \
    #        "Unexpected write response: %#x != %#x" % (calc_offset, resp_offset)

def open_local_writable(path):
    if path == '-':
        try: return (sys.stdout.buffer,0)
        except: return (sys.stdout,0)
    else:
        try:
            s = os.stat(path)
        except OSError:
            s = 0
            f = open(path, "wb")
        else:
            s = s.st_size
            assert not s%BLOCK_SIZE
            f = open(path, "ab")
        return (f,s)


def open_local_readable(path):
    if path == '-':
        try: return sys.stdin.buffer
        except: return sys.stdin
    else:
        return open(path, "rb")

def get_partition_info_string(part, batch):
    if not batch:
        info = '#   Flags From(#s)   To(#s)     GUID/UID                             Type/Name\n'
        info += ('{n: <3} {flags: ^5} {from_s: <10} {to_s: <10} {guid} {type}\n' + ' ' * 32 + '{uid} {name}').format(
                n=part.index, flags=part.flags, from_s=part.first_lba, to_s=part.last_lba, guid=part.guid,
                type=part.type, uid=part.uid, name=part.name)
    else:
        info = ('{name}:{start_sector}:{end_sector}').format(name=part.name, start_sector=part.first_lba, end_sector=part.last_lba)
    return info

def find_misc(comm, fd_num):
    """
    Find the start sector of the misc partition
    (needed for misc write)
    """
    diskinfo = get_partitions(comm, fd_num)
    part = find_partition(diskinfo, "misc")
    part_misc = get_partition_info_string(part, batch=True)
    misc_start = part_misc.split(':')
    _logger.debug("Found misc at disk offset %s", misc_start[1])
    return misc_start[1]

def dict_partition_table(diskinfo, dev, showheader=True):
    """
    catch the partition listing and return the result (dict)
    """
    part_table = {}
    part_header,part_table = gpt.show_disk_partitions_info(diskinfo, BLOCK_SIZE, dev, batch=True, fmtdict=True, showheader=showheader)
    return part_header,part_table

def print_partition(part, pdict, batch=False):
    """
    will print the partition(s) based on batch or not differently
    requires a dict to work with
    """
    if batch:
        print(('{name}:{pt[p_no]}:{pt[p_first_lba]}:{pt[p_last_lba]}:{pt[p_uid]}:{pt[p_size]}').format(name=part,pt=pdict))
    else:
        print(('{pt[p_no]: <3} {pt[p_first_lba]: <10} {pt[p_last_lba]: <10} {pt[p_guid]} {pt[p_type]}\n' + ' ' * 26 + '{pt[p_uid]} {name}').format(name=part,pt=pdict))

def list_partitions(part_header, part_table, part_filter=None, batch=False):
	if part_filter:
            p_found = False
            # list only 1 partition
            for d,v in part_table.items():
                if part_filter in v:
                    p_found = True
                    break
                else:
                    _logger.debug("Partition %s not found in %s.. continue search on next device" % (part_filter, d))
                    continue
            if p_found:
                if not batch: print(part_header[d])
                print_partition(part_filter,v[part_filter], batch)
            else:
                print("Error: Partition %s not found" % part_filter)
	else:
            # list all partitions
	    for d,v in part_table.items():
                if not batch: print(part_header[d])
                for p in v.items():
                    part = p[0]
                    print_partition(part, part_table[d][part], batch)

def dump_partition(comm, disk_fd, local_path, part_offset, part_size, batch=False):
    # Read offsets must be a multiple of 4096 bytes, enforce this
    read_offset = BLOCK_SIZE * (part_offset // BLOCK_SIZE)
    end_offset = part_offset + part_size

    _f,s = open_local_writable(local_path)
    with _f as f:
        read_offset += s
        unaligned_bytes = read_offset % BLOCK_SIZE
        if unaligned_bytes:
            _logger.debug("Unaligned read, read will start at %d", read_offset)
        _logger.debug("Will read %d bytes at disk offset %d", part_size, part_offset)
        # Offset should be aligned to block size. If not, read at most a
        # whole block and drop the leading bytes.
        if unaligned_bytes:
            chunksize = min(end_offset - read_offset, BLOCK_SIZE)
            data, disk_fd = laf_read(comm, disk_fd, read_offset // BLOCK_SIZE, chunksize)
            f.write(data[unaligned_bytes:])
            read_offset += BLOCK_SIZE

        written = 0
        old_pos = -1

        while read_offset < end_offset:
            chunksize = min(end_offset - read_offset, BLOCK_SIZE * MAX_BLOCK_SIZE)
            data, disk_fd = laf_read(comm, disk_fd, read_offset // BLOCK_SIZE, chunksize)
            f.write(data)
            written += len(data)
            read_offset += chunksize
            curr_progress = int(written / part_size * 100)

            _logger.debug("written: %i, part_size: %i , curr_progress: %i",
                           written, part_size, curr_progress)

            if written <= part_size:
                _logger.debug("%i <= %i", written, part_size)
                old_pos = curr_progress
                if not batch:
                  print_human_progress(curr_progress, written, part_size)
                else:
                  print_progress(curr_progress, written, part_size)

        if not batch:
            _logger.info("Wrote %d bytes to %s", part_size, local_path)

class NoDiskFdException(Exception):
    pass

def write_partition(comm, disk_fd, local_path, part_offset, part_size, batch):
    write_offset = BLOCK_SIZE * (part_offset // BLOCK_SIZE)
    end_offset = part_offset + part_size
    # TODO support unaligned writes via read/modify/write
    if part_offset % BLOCK_SIZE:
        raise RuntimeError("Unaligned partition writes are not supported yet")

    # Sanity check
    assert part_offset >= GPT_LBA_LEN * BLOCK_SIZE, "Will not allow overwriting GPT scheme"

    # disable RESTORE until newer LAF communication is fixed! this will not work atm!
    if hex(comm.protocol_version) == '0x1000001':
      with open_local_readable(local_path) as f:
        try:
            length = f.seek(0, 2)
        except OSError:
            # Will try to write up to the end of the file.
            _logger.debug("File %s is not seekable, length is unknown",
                    local_path)
        else:
            # Restore position and check if file is small enough
            f.seek(0)
            if length > part_size:
                raise RuntimeError("File size %d is larger than partition "
                        "size %d" % (length, part_size))
            # Some special bytes report 0 (such as /dev/zero)
            if length > 0:
                _logger.debug("Will write %d bytes", length)

        written = 0
        old_pos = -1
        read_size = 1048576  # 1 MB (anything higher will have 0 effect but this speeds up a lot)
        write_mode = 0x20    # TOT write mode. MM or earlier. Must be uncompressed data.

        while write_offset < end_offset:
            chunksize = min(end_offset - write_offset, read_size)
            data = f.read(chunksize)
            #zdata = zlib.compress(data)
            if not data:
                break # End of file
            write_offset_bs = write_offset // BLOCK_SIZE
            laf_write(comm, disk_fd, write_offset_bs, write_mode, data)
            written += len(data)

            curr_progress = int(written / part_size * 100)
            _logger.debug("disk_fd: %i, written: %i, part_size: %i , curr_progress: %i, write_offset: %i, write_offset_bs: %i, end_offset: %i, part_offset: %i, write_mode: 0x%x",
                           disk_fd, written, part_size, curr_progress, write_offset, write_offset_bs, end_offset, part_offset, write_mode)

            if written <= part_size:
                _logger.debug("%i <= %i", written, part_size)
                old_pos = curr_progress
                if not batch:
                  print_human_progress(curr_progress, written, part_size)
                else:
                  print_progress(curr_progress, written, part_size)

            write_offset += chunksize
            write_mode = 0x00 # Streaming write mode. Only used for TOT writing MM or earlier
            if len(data) != chunksize:
                break # Short read, end of file

        if not batch:
            _logger.info("Done after writing %d bytes from %s", written, local_path)
    else: 
        raise RuntimeError("Your installed firmware %x does not support writing atm. sorry." % comm.protocol_version)

def write_misc_partition(comm, fd_num, local_path, part_offset, part_size, batch):
    write_offset = BLOCK_SIZE * (part_offset // BLOCK_SIZE)
    end_offset = part_offset + part_size
    if part_offset % BLOCK_SIZE:
        raise RuntimeError("Unaligned partition writes are not supported yet")

    # Sanity check
    assert part_offset >= GPT_LBA_LEN * BLOCK_SIZE, "Will not allow overwriting GPT scheme"

    with open_local_readable(local_path) as f:
        try:
            length = f.seek(0, 2)
        except OSError:
            # Will try to write up to the end of the file.
            _logger.debug("File %s is not seekable, length is unknown",
                    local_path)
        else:
            # Restore position and check if file is small enough
            f.seek(0)
            if length > part_size:
                raise RuntimeError("File size %d is larger than partition "
                        "size %d" % (length, part_size))
            # Some special bytes report 0 (such as /dev/zero)
            if length > 0:
                _logger.debug("Will write %d bytes", length)
        # TODO: automatically detect this.
        #misc_start = 262144
        #misc_start = 43014
        misc_start = find_misc(comm, fd_num)
        written = 0
        while write_offset < end_offset:
            # TODO: automatically get the size of misc, but it is hardcoded for now
            # Also, this MUST be divisable by BLOCK_SIZE
            chunksize = BLOCK_SIZE 
            data = f.read(chunksize)
            if not data:
                break # End of file
            if len(data) != chunksize:
                chunksize = len(data)
            # This writes to misc
            laf_misc_write(comm, chunksize, data)
            # This enables write to the FD
            laf_ioct(comm, fd_num,0x1261)
            # This copies the data from misc to your destination partition
            laf_copy(comm, fd_num, misc_start, chunksize, write_offset // BLOCK_SIZE)
            # This disables write on the FD.
            laf_ioct(comm, fd_num,0x1261)

            written += len(data)
            curr_progress = int(written / length * 100)

            if written <= length:
                _logger.debug("%i <= %i", written, length)
                old_pos = curr_progress
                if not batch:
                  print_human_progress(curr_progress, written, length)
                else:
                  print_progress(curr_progress, written, length)

            write_offset += chunksize
            if len(data) != chunksize:
                break # Short read, end of file
        _logger.info("Done after writing %d bytes from %s", written, local_path)

def print_progress(i, current_val, max_val):
    current_val = int(current_val / 1024)
    max_val = int(max_val / 1024)
    print('%i:%i:%i' % (i, current_val, max_val), flush=True)
    #sys.stdout.write('%i:%i:%i\n' % (i, current_val, max_val))
    #sys.stdout.write("\r%d " % i)
    #sys.stdout.flush()

def print_human_progress(i, current_val, max_val):
    current_val = int(current_val / 1024)
    max_val = int(max_val / 1024)
    sys.stdout.write(' (%i / %i KB)' % (current_val, max_val))
    sys.stdout.write("\r [ %d " % i + "% ] ")
    sys.stdout.flush()

def wipe_partition(comm, disk_fd, part_offset, part_size, batch):
    sector_start = part_offset // BLOCK_SIZE
    sector_count = part_size // BLOCK_SIZE

    # Sanity check
    assert sector_start >= 34, "Will not allow overwriting GPT scheme"
    # Discarding no sectors or more than 512 GiB is a bit stupid.
    assert 0 < sector_count < 1024**3, "Invalid sector count %d" % sector_count

    laf_erase(comm, disk_fd, sector_start, sector_count)
    if not batch:
        _logger.info("Done with TRIM from sector %d, count %d (%s)",
            sector_start, sector_count, human_readable(part_size))
    else:
        print("TRIM ok:", sector_start, sector_count, human_readable(part_size))

class SmartFormatter(argparse.HelpFormatter):

    def _split_lines(self, text, width):
        if text.startswith('F|'):
            return text[2:].splitlines()  
        # this is the RawTextHelpFormatter._split_lines
        return argparse.HelpFormatter._split_lines(self, text, width)

parser = argparse.ArgumentParser(formatter_class=SmartFormatter)
parser.add_argument("--cr", choices=['yes', 'no'], help="Do initial challenge response (KILO CENT/METR)")
parser.add_argument("--debug", action='store_true', help="Enable debug messages")
parser.add_argument("--list", action='store_true',
        help='List available partitions. Define a partion name to filter.')
parser.add_argument("--dump", metavar="LOCAL_PATH",
        help="Dump partition to file ('-' for stdout)")
parser.add_argument("--sign", metavar="LOCAL_PATH",
        help="Send sign payload for signed writing ('-' for stdin)")
parser.add_argument("--restore", metavar="LOCAL_PATH",
        help="Write file to partition on device ('-' for stdin)")
parser.add_argument("--restoremisc", metavar="LOCAL_PATH",
        help="Write file to partition on device with MISC WRTE / COPY ('-' for stdin)")
parser.add_argument("--wipe", action='store_true',
        help="TRIMs a partition")
parser.add_argument("partition", nargs='?',
        help="Partition number (e.g. 1 for block device mmcblk0p1)"
        " or partition name (e.g. 'recovery')")
parser.add_argument("--skip-hello", action="store_true", dest="skip_hello",
        help="Immediately send commands, skip HELO message")
parser.add_argument("--batch", action="store_true",
        help="Print partition list in machine readable output format")
parser.add_argument("--devtype", choices=['UFS', 'EMMC'],
        help="Force the device type (UFS or EMMC)")
parser.add_argument("--lun", choices=['sda', 'sdb', 'sdc', 'sdd', 'sde', 'sdf', 'sdg'],
        help="Specify which lun to work with on UFS devices")
parser.add_argument("--proto", nargs='?',
        help="F|Forces a specific protocol version, skips protocol negotiation.\n \
Format:\n\
--proto 0x1000003 for version 3\n\
--proto 0x1000018 for version 18")

def close_fd(comm, fd_num):
    """
    close a file descriptor
    """
    cr_needed = lglaf.chk_mode(comm.protocol_version,comm.CR_NEEDED,comm.CR_MODE)
    close_cmd = lglaf.make_request(b'CLSE', args=[fd_num])
    if cr_needed == 1:
        lglaf.challenge_response(comm, 4)
    comm.call(close_cmd)

def detect_and_open_fd(comm, args):
    """
    detects the required disk opener
    and 
    """
    part_header = {}
    part_table = {}

    for dev,opencmd in disk_opener.items():
      disk_fd = laf_open_disk(comm, opencmd)
      if disk_fd: 
        _logger.debug("opened a disk_fd: %i on %s" % (disk_fd, dev))
        # detect the device type and based on that set the block size and GPT LBA length
        # atm we know just 2 block sizes, one for EMMC devices and one for UFS
        # as those will likely not change in the near future I hardcode both here
        global BLOCK_SIZE,GPT_LBA_LEN,MAX_BLOCK_SIZE
        BLOCK_SIZE_UFS = 4096
        BLOCK_SIZE_EMMC = 512
        GPT_LBA_LEN_UFS = 6
        GPT_LBA_LEN_EMMC = 34

        # Note for calculating MAX_BLOCK_SIZE:
        # On Linux, one bulk read returns at most 16 KiB. 32 bytes are part of the first
        # header, so remove one block size (512 bytes) to stay within that margin.
        # This ensures that whenever the USB communication gets out of sync, it will
        # always start with a message header, making recovery easier.

        if not args.devtype:
            # as we are moving forward we expect UFS devices first(!)
            BLOCK_SIZE = BLOCK_SIZE_UFS
            GPT_LBA_LEN = GPT_LBA_LEN_UFS
            MAX_BLOCK_SIZE = (16 * 1024 - BLOCK_SIZE) // BLOCK_SIZE
            if check_block_size(comm, disk_fd):
                devtype = "UFS"
            else:
                BLOCK_SIZE = BLOCK_SIZE_EMMC
                GPT_LBA_LEN = GPT_LBA_LEN_EMMC
                MAX_BLOCK_SIZE = (16 * 1024 - BLOCK_SIZE) // BLOCK_SIZE
                if check_block_size(comm, disk_fd):
                    devtype = "EMMC"
                else:
                    _logger("Cannot identify the block size!")
                    raise
        else:
            if args.devtype == "UFS":
                BLOCK_SIZE = BLOCK_SIZE_UFS
                GPT_LBA_LEN = GPT_LBA_LEN_UFS
                MAX_BLOCK_SIZE = (16 * 1024 - BLOCK_SIZE) // BLOCK_SIZE
            else:
                BLOCK_SIZE = BLOCK_SIZE_EMMC
                GPT_LBA_LEN = GPT_LBA_LEN_EMMC
                MAX_BLOCK_SIZE = (16 * 1024 - BLOCK_SIZE) // BLOCK_SIZE
            devtype = args.devtype
            if check_block_size(comm, disk_fd):
                _logger.debug("enforced device type to: %s" % devtype)
            else:
                parser.error("Cannot identify the GPT header for the forced device type: %s!" % devtype)
                raise

        _logger.debug("GPT_LBA_LEN: %s", GPT_LBA_LEN)
        _logger.debug("BLOCK_SIZE: %s (%s), MAX_BLOCK_SIZE: %s", BLOCK_SIZE, devtype, MAX_BLOCK_SIZE)

        if args.sign:
            fsig = open(args.sign, 'rb')
            sign_payload = fsig.read()
            laf_sign(comm, sign_payload)

        # sda and default are identical - for reading at least.
        # we skip sda for reading but not for anything else
        if dev != "sda":
            diskinfo = get_partitions(comm, disk_fd)
            if args.batch:
                part_header[dev],part_table[dev] = dict_partition_table(diskinfo, dev, showheader=False)
            else:
                part_header[dev],part_table[dev] = dict_partition_table(diskinfo, dev, showheader=True)
        close_fd(comm,disk_fd)
        if devtype == "EMMC": break
      else: break
    return devtype, part_header, part_table

def list_filtered(part_table, args):
    """
    filter partition table dict for given part name
    and identify the required disk opener
    """
    part_opener = None
    filtered_ptable = None

    for dev,p in part_table.items():
        try:
            if part_table[dev][args.partition]:
                filtered_ptable = part_table[dev][args.partition]
                part_opener = disk_opener[dev]
                break
            else: continue
        except KeyError:
            continue
        except ValueError as e:
            parser.error(e)
    if part_opener is None:
        part_opener = disk_opener['default']
    return dev, part_opener, filtered_ptable

def main():
    args = parser.parse_args()
    logging.basicConfig(format='%(asctime)s %(name)s: %(levelname)s: %(message)s',
            level=logging.DEBUG if args.debug else logging.INFO)

    actions = (args.list, args.dump, args.restore, args.restoremisc, args.wipe)
    if sum(1 if x else 0 for x in actions) != 1:
        parser.error("Please specify one action from"
        " --list / --dump / --restore /--restoremisc / --wipe")
    if not args.partition and (args.dump or args.restore or args.wipe):
        parser.error("Please specify a partition")

    if args.partition and args.partition.isdigit():
        args.partition = int(args.partition)

    if args.proto:
        pattern = re.compile("^0x1([0-9]{6,6})$")
        if not pattern.match(args.proto):
            _logger.error("Wrong format (%s) for protocol version! Check --help." % args.proto)
            return
        hex_proto = int(args.proto,16)
        _logger.warning("Forcing protocol to %x" % hex_proto)
        lglaf.BASE_PROTOCOL_VERSION = hex_proto

    comm = lglaf.autodetect_device(args.cr)
    with closing(comm):

        if not args.skip_hello:
            lglaf.try_hello(comm, lglaf.BASE_PROTOCOL_VERSION)

            if comm.protocol_negotiation:
                lglaf.try_hello(comm, DEV_PROTOCOL_VERSION=comm.protocol_version)
                _logger.debug("Negotiated protocol version: 0x%x" % comm.protocol_version)
        else:
            _logger.debug("Used protocol version: %07x" % comm.protocol_version)

        if not args.lun:
            lun = sda_body

        if args.lun == "sda":
            lun = sda_body
        elif args.lun == "sdb":
            lun = sdb_body
        elif args.lun == "sdc":
            lun = sdc_body
        elif args.lun == "sdd":
            lun = sdd_body
        elif args.lun == "sde":
            lun = sde_body
        elif args.lun == "sdf":
            lun = sdf_body
        elif args.lun == "sdg":
            lun = sdg_body

        devtype, part_header, part_table = detect_and_open_fd(comm, args)

        # list all or get a filtered partition list
        if args.list:
            list_partitions(part_header, part_table, args.partition, args.batch)
        else:
            dev, part_opener, filtered_ptable = list_filtered(part_table, args)

            _logger.debug("Found partition on device: %s" % dev)
            part_offset = filtered_ptable['p_first_lba'] * BLOCK_SIZE
            part_size = (filtered_ptable['p_last_lba'] - (filtered_ptable['p_first_lba'] - 1)) * BLOCK_SIZE

            _logger.debug("part offset: %i, size: %i", part_offset, part_size)
            _logger.debug("opener: %s" % part_opener)

            disk_fd = laf_open_disk(comm, part_opener)
            _logger.debug("opened a disk_fd: %i on %s" % (disk_fd, dev))

            if args.dump:
                dump_partition(comm, disk_fd, args.dump, part_offset, part_size, args.batch)
            elif args.restore:
                if not args.batch:
                    write_partition(comm, disk_fd, args.restore, part_offset, part_size, False)
                else:
                    write_partition(comm, disk_fd, args.restore, part_offset, part_size, True)
            elif args.restoremisc:
                if not args.batch:
                    write_misc_partition(comm, disk_fd, args.restoremisc, part_offset, part_size, False)
                else:
                    write_misc_partition(comm, disk_fd, args.restoremisc, part_offset, part_size, True)
            elif args.wipe:
                if not args.batch:
                    wipe_partition(comm, disk_fd, part_offset, part_size, False)
                else:
                    wipe_partition(comm, disk_fd, part_offset, part_size, True)
            close_fd(comm,disk_fd)

if __name__ == '__main__':
    try:
        main()
    except OSError as e:
        # Ignore when stdout is closed in a pipe
        if e.errno != 32:
            raise

