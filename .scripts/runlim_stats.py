from array import array
import re

# Read every lines from an input file into an array
def read_lines(filename):
    with open(filename, 'r') as f:
        return f.readlines()

# Parse a line into a structure of the following fields:
#   - query_id
#   - query_timing
def parse_line(line):
    line = line.strip()
    # a regular expression to parse the line starting from the pattern 'Query-stats'
    # The next field is delimited by parentheses
    # Then the constant "succeeded in" or "succeeded (with hint) in" follows
    # The the timing field appears
    # All fields are separated by whitespace
    pattern = re.compile(r'RUNLIM: (.+)\s+(\d+.\d+) s\s+(\d+) MB')
    match = pattern.match(line)
    if match is not None:
        program_name = match.group(1)
        return (program_name, match.group(2), match.group(3))
    else:
#        print("Failed to parse line: " + line)
        return None
    
# read lines from a file and parse them retaining only the lines that parse correctly
def read_and_parse_lines(filename):
    lines = read_lines(filename)
    parsed_lines = []
    for line in lines:
        parsed_line = parse_line(line)
        if parsed_line is not None:
            parsed_lines.append(parsed_line)
    return parsed_lines

# join two arrays of parsed lines on the query id
def join_lines(lines1, lines2):
    joined_lines_space = []
    joined_lines_time = []
    for line1 in lines1:
        time1 = float(line1[1])
        space1 = float(line1[2])
        for line2 in lines2:
            if line1[0] == line2[0]:
                time2 = float(line2[1])
                space2 = float(line2[2])                
                joined_lines_time.append((line1[0], time1, time2, ((time2 - time1) / time1) * 100))
                joined_lines_space.append((line1[0], space1, space2, ((space2 - space1) / space1) * 100))
    return (joined_lines_space, joined_lines_time)

# sort the joined lines by the maximum difference in query timing
def sort_lines(joined_lines):
    joined_lines.sort(key=lambda x: x[3])
    return joined_lines

# print the joined lines
def print_lines(joined_lines, units, n):
    for line in joined_lines[-n:]:
        queryid = line[0]
        pctg = "{:.2f}".format(line[3])
        print(queryid + str(line[1]) + ", " + str(line[2]) + ", " + pctg + "% " + units)

# find entries in joined array with the same query id
def find_duplicates(joined_lines):
    duplicates = []
    for i in range(len(joined_lines)):
        if joined_lines[i][0] in duplicates:
            continue
        for j in range(i+1, len(joined_lines)):
            if joined_lines[i][0] == joined_lines[j][0]:
                duplicates.append(joined_lines[j][0])
                break
    return duplicates

# if multiple entires in parsed_lines have the same query id,
# retain only the first one
def filter_duplicates(parsed_lines):
    filtered_lines = []
    seen_query_ids = []
    for line in parsed_lines:
        if line[0] not in seen_query_ids:
            filtered_lines.append(line)
            seen_query_ids.append(line[0])
    return filtered_lines


def generate_scatter_plot(sorted_lines, xlabel, ylabel, title):
    import matplotlib.pyplot as plt
    import numpy as np
    # create an array of the query timing differences
    x_axis = []
    y_axis = []
    for line in sorted_lines:
        x_axis.append(float (line[1]))
        y_axis.append(float (line[2]))
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
    print (title + " slope: " + str(b))
    #print (title + "intercept: " + str(a))
    # Create sequence of 100 numbers from 0 to 100 
    # find the maximum of the x_axis
    max_x = max(x_axis)
    xseq = np.linspace(0, max_x, num=1000)

    # Plot regression line
    plt.plot(xseq, a + b * xseq, color="k", lw=2.5);

    # add a title
    plt.title("F* runlim " + title + "; Linear regression slope = " + str(b))

    plt.show()

# read two command line arguments and return them as a pair
def get_command_line_args():
    import sys
    if len(sys.argv) != 3:
        print("Usage: " + sys.argv[0] + " <file1> <file2>")
        sys.exit(1)
    return sys.argv[1], sys.argv[2]

# find all entries in first array that are not in the second array
def find_differences(lines1, lines2):
    differences = []
    for line1 in lines1:
        if line1 not in lines2:
            differences.append(line1)
    return differences

# main function
def main():
    # get the command line arguments
    file1, file2 = get_command_line_args()
    # read the input file
    lines1 = filter_duplicates(read_and_parse_lines(file1))
    lines2 = filter_duplicates(read_and_parse_lines(file2))
    print("parsed " + str(len(lines1)) + " lines from file1")
    print("parsed " + str(len(lines2)) + " lines from file2")
    joined_lines = join_lines(lines1, lines2)
    # sort the lines
    sorted_space_lines = sort_lines(joined_lines[0])
    sorted_time_lines = sort_lines(joined_lines[1])
    #
    print_lines (sorted_space_lines, "MB", 20)
    print_lines (sorted_time_lines, "seconds", 20)    
    # generate a scatter plot
    generate_scatter_plot(sorted_space_lines, file1, file2, "space (MB)")
    generate_scatter_plot(sorted_time_lines, file1, file2, "time (s)")


main()
