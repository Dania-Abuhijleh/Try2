from setuptools import find_packages, setup

from codecs import open
from os import path

HERE = path.abspath(path.dirname(__file__))

with open(path.join(HERE, 'README.md'), encoding='utf-8') as f:
    long_description = f.read()

setup(
    name='formula-generator',
    packages=find_packages(include=['project', 'project.package', 'project.package.parse']),
    include_package_data=True,
    version='0.1.1',
    description='My first Python library',
    url="https://formula-generator.readthedocs.io/",
    author='Dania',
    license='MIT',
    install_requires=['click', 'pythonds'],
)
