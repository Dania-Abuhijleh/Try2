# fall-2021

This program takes a propositional formula and returns a list of formulas similar to the original one by substituting the operations in all possible combinations. You must provide a list of lists of operators, the operators in the same list can be substituted for one another. For example if I provide [['∨', '∧'], ['→', '↔'], ['¬']] this means '∨' and '∧' are interchangable for each other but not for '¬'. Mathematical operators and integers are also supported.

Check the example files to see the syntax. Input a file with the formula on one line (SMT 2.0 format) and the list of lists of operators (z3 format) on the next line. SMT 2.0 is described here https://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.0-r10.12.21.pdf

# Linux

Download Python

Download Git

Download z3:
```
git clone https://github.com/Z3Prover/z3.git
cd z3
python3 scripts/mk_make.py --python
cd build
make
sudo make install

pip3 install z3-solver
```
also do `pip3 install pythonds`

then download this repo by downloading the .zip file and extracting it.
then run an example file like so:
Navigate to the directory where main.py is in your terminal and invoke the command: python main.py '/path/to/example.txt'

# Windows
Download Python:
Open the official python website and navigate to the download tab for Windows https://www.python.org/downloads/windows/. Click on the latest python release and download a Windows executable installer suitable for your system (check to make sure you download 32-bit installer if your system is 32-bit, and 64-bit installer otherwise). 
![image](https://user-images.githubusercontent.com/57302458/130057266-f36c80a5-2f9d-4732-b26f-2fe97549bdf7.png)

Once it is downloaded run the installer. Check the Install launcher for all users check box and check the Add Python 3.7 to path check box to include the interpreter in the execution path. Then select Customize installation and choose all the optional features. Click next. This takes you to Advanced Options available while installing Python. Here, select the Install for all users and Add Python to environment variables check boxes. Select the Associate files with Python, Create shortcuts for installed applications and other advanced options. Make note of the python installation directory displayed in this step. You would need it for the next step.
After selecting the Advanced options, click Install to start installation. Verify the python installation by searching for the command prompt and type “python”. (Instructions from https://www.journaldev.com/30076/install-python-windows-10)

Download Git if you do not already have it.

Download Z3: For Windows, this requires a Visual Studio command prompt. Download VS for windows if you don't have it. As documented here: https://docs.microsoft.com/en-us/visualstudio/ide/reference/command-prompt-powershell?view=vs-2019 Then on the start menu under Visual Studio click the drop down next to the folder. You should see something similar to 'x64 Native Tools Command Prompt for VS 2017' It doesn't have to be the 2017 version as this is just an example. Click on it and you will see a VS command prompt open. Another example of how to do this here: https://edk2-docs.gitbook.io/uefi_driver_hii_win_lab_guide/microsoft_windows_10__visual_studio_command_prompt
Now type the commands below (if you have x64 bit python then the third line should be `python3 scripts/mk_make.py -x --python` to download the 64 bit version of Z3) **Note: if you have x64 version of Python then you must download the x64 DLL of z3 otherwise errors will arise.**
```
git clone https://github.com/Z3Prover/z3.git
cd z3
python scripts/mk_make.py --python
cd C:\...\z3\build && nmake
```
Where C:\...\z3\build is the path to \z3\build on your computer.

Go to your System Environment Variables and add the 'build\python' directory in your z3 folder to the PYTHONPATH environment variable and add the 'build' directory to the PATH environment variable. Also add 'C:\...\Python\Python39\Scripts' (just an example use the Python path from your computer that ends with \Scripts) to the PATH environment variable.

Next download pip if you don't already have it. `curl https://bootstrap.pypa.io/get-pip.py -o get-pip.py`

Next do `pip install pythonds` and `pip install click`

Note that you may have to restart your command prompt after downloading anything.

Now we are ready to run the example file.

Download this repo by downloading the .zip file and extracting it.
Still in your command prompt, Navigate to the folder that contains main.py `cd C:\...\project` and run this command `python main.py C:\...\examples\example1.txt` 

If you run into issues check that your bit versions of python and z3 are compatible (i.e. both 32 bit or both 64 bit). If that is fine check that you added the mentioned paths to your system environment variables.
