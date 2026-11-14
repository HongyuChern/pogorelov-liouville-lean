#!/usr/bin/env python3
"""Reuse an existing, clean pinned local workspace's dependency checkouts/caches.

Only creates links in the destination .lake/packages. Does not launch Codex,
Work, remote agents, builds, or paid services. No source checkout is modified.
"""
from pathlib import Path
import argparse
import json
import subprocess

ROOT=Path(__file__).resolve().parents[1]

def git(path,*args):
    return subprocess.check_output(['git','-C',str(path),*args],text=True).strip()

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('workspace',type=Path)
    args=parser.parse_args()
    parent=args.workspace.resolve()/'.lake/packages'
    target=ROOT/'.lake/packages'
    packages=json.loads((ROOT/'lake-manifest.json').read_text())['packages']
    plan=[]
    for package in packages:
        name=package['name'];expected=package['rev']
        dest=target/name
        source=dest if dest.exists() else parent/name
        if not source.is_dir() or git(source,'rev-parse','HEAD')!=expected:
            raise RuntimeError('Missing or wrong pinned checkout: '+str(source))
        if git(source,'status','--porcelain','--untracked-files=no'):
            raise RuntimeError('Tracked sources modified: '+str(source))
        if dest.is_symlink() and not dest.exists():
            raise RuntimeError('Dangling destination link: '+str(dest))
        plan.append((name,source.resolve(),dest,expected))
    target.mkdir(parents=True,exist_ok=True)
    for name,source,dest,rev in plan:
        if not dest.exists():dest.symlink_to(source,target_is_directory=True)
        print(name,rev,'->',source)
    print('Pinned local package checkouts reused. No Lean compilation performed.')

if __name__=='__main__':main()
