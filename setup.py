## -*- encoding: utf-8 -*-
"""
A semigroup (representation) theory library for SageMath
"""

import os
import sys
# Always prefer setuptools over distutils
from setuptools import setup, find_packages
from setuptools.command.test import test as TestCommand
# To use a consistent encoding
from codecs import open

here = os.path.abspath(os.path.dirname(__file__))

# Get the long description from the README file
with open(os.path.join(here, 'README.rst'), encoding='utf-8') as f:
    long_description = f.read()

class SageTest(TestCommand):
    def run_tests(self):
        errno = os.system("sage -t sage_semigroups")
        sys.exit(errno)

setup(
    name='sage-semigroups',
    version='0.1.0',
    description='A semigroup (representation) theory library for SageMath',
    long_description=long_description,
    url='https://github.com/nthiery/sage-semigroups',
    author='Nicolas M. Thiéry',
    author_email='nthiery@users.sf.net',
    license='GPLv3',
    classifiers=[
        'Development Status :: 3 - Alpha',
        'Intended Audience :: Science/Research'
        'Topic :: Software Development :: Build Tools',
        'Topic :: Scientific/Engineering :: Mathematics',
        'License :: OSI Approved :: GNU General Public License (GPL)',
        'Programming Language :: Python :: 2',
        #'Programming Language :: Python :: 3',
    ],
    keywords='SageMath, semigroup theory',
    packages=find_packages(),
    install_requires=['recursive-monkey-patch'],
    cmdclass = {'test': SageTest},
)
