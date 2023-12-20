import os
import shutil
import sys
import argparse

import pycparser.plyparser
import random
import traceback
import pathlib

from glob import glob
from time import time

from tqdm import tqdm

import smt_lib2c
from mapreduce import mapreduce


# Transformer ---------------------------------------------------------------------------

class FileTransformer:

    def __init__(self, config):
        self._output_dir = config.output_dir
        self._recursion_limit = config.recursion_limit
        self._preserve_structure = config.preserve_structure
        self._prefix = config.prefix
        self._suffix = config.suffix
        self._header = config.header
        self._timeout = config.timeout
        if config.header_file:
            with open(config.header_file, 'r') as r:
                self._header = r.read()

        try:
            self.git_hash = os.popen('git rev-parse --short head').read().splitlines()[0]
        except IndexError:
            self.git_hash = 'unknown'

    def __call__(self, file_name):
        filesize = os.stat(file_name).st_size // 1024
        maxsize = 128
        if filesize > maxsize:
            print(f"\nFile '{file_name}' exceeds maximal file size and will be ignored ({filesize} kB > {maxsize} kB).")
            return [{
                "source_file": file_name,
                "exception"  : f"maximal file size exceeded ({filesize} kB > {maxsize} kB)"
            }]

        sys.setrecursionlimit(self._recursion_limit)


        start_time = time()

        try:

            with open(file_name, 'r') as f:
                transformed = smt_lib2c.main(f, timeout=self._timeout)
        except pycparser.plyparser.ParseError as pe:
            print(f"\ncould not parse '{file_name}' because of {pe}. See statistics for detailed info.")
            return [{
                "source_file": file_name,
                "exception"  : traceback.format_exc(),
                "walltime"   : time() - start_time,
            }]
        except ValueError as ve:
            return [{
                "source_file": file_name,
                "unsupported": list(map(str, ve.args)),
                "exception"  : traceback.format_exc(),
                "walltime"   : time() - start_time,
            }]
        except TimeoutError:
            return [{
                "source_file": file_name,
                "exception": traceback.format_exc(),
                "walltime": time() - start_time,
            }]
        except Exception:
            traceback.print_exc()
            return [{
                "source_file": file_name,
                "exception"  : traceback.format_exc(),
                "walltime"   : time() - start_time,
            }]

        output_files = []
        for i, (c_code, info) in enumerate(transformed):
            input_path, ext = os.path.splitext(file_name)
            basename = os.path.basename(input_path)

            path_parts = [self._output_dir]
            if self._preserve_structure:
                path_parts.append(self._prefix + os.path.basename(os.path.dirname(file_name)) + self._suffix)
            path_parts.append(self._prefix + basename + self._suffix)
            output_path = os.path.join(*path_parts)
            if len(transformed) > 1:
                output_path += f'-{i}'

            with open(output_path + '.yml', 'w+') as w:
                w.write(f"format_version: '2.0'\n\n"
                        f"input_files: '{os.path.basename(output_path)}.c'\n\n"
                        f"properties:\n"
                        f"  - property_file: ../properties/unreach-call.prp\n"
                        f"    expected_verdict: {'false' if info[':status'] == 'sat' else 'true'}\n\n"
                        f"options:\n"
                        f"  language: C\n"
                        f"  data_model: ILP32\n"
                        f"\n# original_file: {os.path.basename(input_path)}.smt2")

            with open(output_path + '.c', "w") as o:
                o.write(
                    self._header
                        .replace('\\n', '\n').replace('\\r', '\r')
                        .replace('{input_file}', os.path.basename(input_path) + ext)
                        .replace('{output_file}', os.path.basename(output_path) + ext)
                        .replace('{commit_hash}', self.git_hash)
                        .format(**info)
                )
                o.write(c_code)
            
            output_files.append({"c_file_path": f'{output_path}.c', "yml_file_path": f'{output_path}.yml'})

        return [{
            "source_file": file_name, 
            "output"     : output_files,
            "walltime"   : time() - start_time
        }]
        


# Parsing input arguments ----------------------------------------------------------------

def dedup_input_files(args, input_files):
    
    def _exists(file_name):
        output_path = os.path.join(args.output_dir, os.path.basename(file_name))
        return not os.path.exists(output_path)

    return list(filter(_exists, input_files))


def prepare_parser():
    parser = argparse.ArgumentParser()
    parser.add_argument("input_files", nargs = "+",
                        help = ".sml2 files to transform")
    parser.add_argument("-o", "--output_dir", type = str, required = True,
                        help = "file to put the transformed files into")
    parser.add_argument("--timeout", type = float,
                        help = "timeout for each file in s")
    parser.add_argument("--recursion_limit", type = int, default = 30000,
                        help = "limits the recursion depht while traversing the abstract syntax tree")
    parser.add_argument("--prefix", type = str, default = '', help = "prefix for folder and file names")
    parser.add_argument("--suffix", type = str, default = '', help = "suffix for folder and file names")
    parser.add_argument("--header", type = str, default = '', help = "header prefixed to transformed sources files")
    parser.add_argument("--header_file", type = str, default = '', help = "path to header text")
    parser.add_argument("--no_dedup", action = "store_true", help = "prevents overriding of already existing files")

    parser.add_argument("--parallel", action = "store_true",
                        help = "makes the transformation of different files run in parallel")
    parser.add_argument("--preserve_structure", action = "store_true",
                        help = "keeps the folder structure of the original")

    return parser


def copy_info_files(folder, folder_out):
    if not os.path.exists(folder_out):
        os.makedirs(folder_out)
    for file in os.listdir(folder):
        if 'license' in os.path.basename(file).lower():
            shutil.copy(os.path.join(folder, file), os.path.join(folder_out, file))
        if 'readme' in os.path.basename(file).lower():
            with open(os.path.join(folder, file), 'r') as r:
                readme = r.read()
            with open(os.path.join(folder_out, file), 'w+') as w:
                w.write(f'{readme}\n\ntransformed with semtransforms\n'
                        f'https://github.com/Flo0112358/semtransforms')


def main(*args):
    args = prepare_parser().parse_args(args)

    print("Search for input files...")

    input_files = [str(path) for pathspec in args.input_files for path in pathlib.Path('').glob(pathspec)]

    if args.no_dedup:
        input_files = dedup_input_files(args, input_files)

    # Guarantees that files of similar complexity are batched together
    input_files = sorted(input_files, key = lambda path: os.stat(path).st_size)

    print(f"Found {len(input_files)} files...\n"
          f"Start transformation...")
    
    transformer = FileTransformer(args)

    if args.preserve_structure:
        folders = {os.path.dirname(file) for file in input_files}
        for folder in folders:
            basename = args.prefix + os.path.basename(folder) + args.suffix
            copy_info_files(folder, os.path.join(args.output_dir, basename))

    # Run mapreduce
    mapreduce(input_files, transformer, reducer_fn = args.output_dir, parallel = args.parallel, report = True)


if __name__ == '__main__':
    main(*sys.argv[1:])
