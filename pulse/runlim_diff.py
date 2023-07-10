#!/usr/bin/env python3

# This script compares two runlim runs and produces a scatter plot with linear regression
#
# It takes as input two identifiers, the identifiers for the new run and the old run resp.
#
# Suppose the requirement is to compare the runlim runs across two branches b1 and b2
# First you would git checkout b1, and run F* with RESOURCEMONITOR=1 and MONID=1 (or any other identifier)
# Then you would git checkout b2, and run F* with RESOURCEMONITOR=1 and MONID=2 (or something else)
# And then you can invoke this script as `python3 runlim_diff.py 2 1`,
#   and it would compare the run 2 with the baseline run 1
#
# It can be used across local changes also, not just to compare two branches
#

# a function that takes as input a filename, 2 hashtables, and a line
# it removes the "[runlim] " prefix from the line
# it splits the rest of the line into a list of strings
# if the first element of the list is "time:", it adds the filename and the second string to the first hashtable
# if the first element of the list is "space:", it adds the filename and the second string to the second hashtable
# it returns the two hashtables
def parse_line(filename, time, space, line):
    line = line.replace("[runlim] ", "")
    line = line.split()
    if line[0] == "time:":
        time[filename] = line[1]
    elif line[0] == "space:":
        space[filename] = line[1]
    return time, space


# a function that takes as input a filename, an identifier, and 2 hashtables
# it opens the file and reads each line
# it strips .identifier".runlim" from the filename
# it calls parse_line on the on the resulting string, the 2 hashtables, and each line
# it returns the 2 hashtables
def parse_file(filename, identifier, dire, time, space):
    file_id = filename
    if identifier != "":
      file_id = file_id.replace(".{}.runlim".format(identifier), "")
    if dire != "":
      file_id = file_id.replace(".runlim".format(identifier), "")
      file_id = file_id.replace(dire + "/", "")

    with open(filename) as f:
        for line in f:
            time, space = parse_line(file_id, time, space, line)
    return time, space


# a function that takes as input a directory
# it lists all the files in the directory recursively
# it returns the list of files


def list_files(directory):
    import os
    files = []
    for filename in os.listdir(directory):
        if os.path.isfile(os.path.join(directory, filename)):
            files.append(os.path.join(directory, filename))
        else:
            files = files + list_files(os.path.join(directory, filename))
    return files


# a function that takes as input an identifier
# it creates 2 empty hashtables
# it calls list_files on "." (the current directory)
# it calls parse_file on all the files in the list with suffix .identifier".runlim"
# it returns the 2 hashtables
def parse_all(identifier):
    time = {}
    space = {}
    files = list_files(".")
    for filename in files:
        if filename.endswith(".{}.runlim".format(identifier)):
            time, space = parse_file(filename, identifier, "", time, space)
    return time, space

def parse_dir(dire):
    time = {}
    space = {}
    files = list_files(dire)
    for filename in files:
        if filename.endswith(".runlim"):
            time, space = parse_file(filename, "", dire, time, space)
    return time, space

# a function that takes as input 2 hashtables
# it creates one array
# it iterates over the keys of the first hashtable
# it adds the tuple (key, value in the first hashtable, value in the second hashtable, percentage difference of values of the first and second hashtables) to the array
# it returns the array


def diff_hashtables(hashtable1, hashtable2):
    diff = []
    for key in hashtable2:
        if float(hashtable2[key]) == 0:
            print(key + " has zero value?")
        elif key in hashtable1:
            diff.append((key, hashtable1[key], hashtable2[key], (float(
                hashtable1[key]) - float(hashtable2[key])) / float(hashtable2[key]) * 100))
        else:
            print(key + " is in the base run but not the new run, dropping")
    return diff

# a function that takes as input an array of tuples
# it sorts the array by the third element of the tuples
# it returns the sorted array


def sort_array(array):
    return sorted(array, key=lambda x: x[2])

# generate_scatter_plot is lift and shift from runlim_stats.py

def generate_scatter_plot(sorted_lines, xlabel, ylabel, title):
    import matplotlib.pyplot as plt
    import numpy as np
    # create an array of the query timing differences
    x_axis = []
    y_axis = []
    for line in sorted_lines:
        x_axis.append(float(line[2]))
        y_axis.append(float(line[1]))
    # plot the query timing differences
    plt.scatter(x_axis, y_axis)
    # label x-axis as xlabel
    plt.xlabel(xlabel)
    # label y-axis as ylabel
    plt.ylabel(ylabel)
    # add a linear regression line
    # Fit linear regression via least squares with numpy.polyfit
    # It returns an slope (b) and intercept (a)
    # deg=1 means linear fit (i.e. polynomial of degree 1)
    b, a = np.polyfit(x_axis, y_axis, deg=1)
    print(title + " slope: " + str(b))
    #print (title + "intercept: " + str(a))
    # Create sequence of 100 numbers from 0 to 100
    # find the maximum of the x_axis
    max_x = max(x_axis)
    xseq = np.linspace(0, max_x, num=1000)

    # Plot regression line
    plt.plot(xseq, a + b * xseq, color="k", lw=2.5)

    # add a title
    plt.title(title + "; Linear regression slope = " + str(b))

    plt.show()

# a function that takes as input a hashtable
# it prints the hashtable
# it exits the program


def print_hashtable(hashtable):
    import sys
    for key in hashtable:
        print(key + " " + hashtable[key])
    sys.exit(0)

# a function that takes as input two identifiers
# it calls parse_all on the first identifier
# it calls parse_all on the second identifier
# it calls diff_hashtables on the two hashtables
# it calls sort_array on the two arrays
# it calls generate_scatter_plot on the two arrays with xlabel as the second identifier and ylabel as the first identifier and title as "F* runlim"

def load_files(isdir, id):
    if isdir:
        time, space = parse_dir(id)
    else:
        time, space = parse_all(id)
    return time, space

def diff(id1, time1, space1, id2, time2, space2):
    time_diff = diff_hashtables(time1, time2)
    space_diff = diff_hashtables(space1, space2)
    time_diff = sort_array(time_diff)
    space_diff = sort_array(space_diff)
    generate_scatter_plot(
        time_diff, "ID " + id2, "ID " + id1, "F* runlim time")
    generate_scatter_plot(
        space_diff, "ID " + id2, "ID " + id1, "F* runlim space")

# main function that parses two identifiers from the command line
# it calls diff on the two identifiers
def main():
    import sys
    import argparse

    parser = argparse.ArgumentParser()
    parser.add_argument("--dirs", action='store_true', help="interpret runs as directories, else as MONID suffixes")
    parser.add_argument("run1", help="the new run")
    parser.add_argument("run2", help="the old run")
    args = parser.parse_args()

    #  if len(args) != 2:
    #      print("Usage: python diff_runlim.py identifier1(the new run) identifier2(the old run)")
    #      print("       python diff_runlim.py --dirs directory1 directory2")
    #      return

    print ("Comparing {} and {}, --dirs={}".format(args.run1, args.run2, args.dirs))

    id1 = args.run1
    id2 = args.run2

    # Remove trailing slashes
    id1 = id1.rstrip('/')
    id2 = id2.rstrip('/')

    t1, s1 = load_files(args.dirs, id1)
    t2, s2 = load_files(args.dirs, id2)

    diff(id1, t1, s1, id2, t2, s2)

main()
