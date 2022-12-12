# a function that takes as input a filename, 3 hashtables, and a line
# it removes the "[runlim] " prefix from the line
# it splits the rest of the line into a list of strings
# if the first element of the list is "real:", it adds the filename and the second string to the first hashtable
# if the first element of the list is "time:", it adds the filename and the second string to the second hashtable
# if the first element of the list is "space:", it adds the filename and the second string to the third hashtable
# it returns the three hashtables
def parse_line(filename, real_times, user_times, space, line):
    line = line.replace("[runlim] ", "")
    line = line.split()
    if line[0] == "real:":
        real_times[filename] = line[1]
    elif line[0] == "time:":
        user_times[filename] = line[1]
    elif line[0] == "space:":
        space[filename] = line[1]
    return real_times, user_times, space

# a function that takes as input a filename, an identifier, and 3 hashtables
# it opens the file and reads each line
# it strips .identifier".runlim" from the filename
# it calls parse_line on the on the resulting string, the 3 hashtables, and each line
# it returns the 3 hashtables
def parse_file(filename, identifier, real_times, user_times, space):
    with open(filename) as f:
        for line in f:
            filename = filename.replace(".{}.runlim".format(identifier), "")
            real_times, user_times, space = parse_line(filename, real_times, user_times, space, line)
    return real_times, user_times, space

# a function that takes as input an identifier
# it creates 3 empty hashtables
# it calls parse_file on all the files in the current directory with suffix .identifier".runlim"
# it returns the 3 hashtables
def parse_all(identifier):
    real_times = {}
    user_times = {}
    space = {}
    for filename in os.listdir("."):
        if filename.endswith(".{}.runlim".format(identifier)):
            real_times, user_times, space = parse_file(filename, identifier, real_times, user_times, space)
    return real_times, user_times, space

# a function that takes as input 2 hashtables
# it creates a third hashtable
# it iterates over the keys of the first hashtable
# it adds the key and the percentage difference of values of the first and second hashtables to the third hashtable
# it returns the third hashtable
def diff_hashtables(hashtable1, hashtable2):
    diff = {}
    for key in hashtable1:
        diff[key] = (float(hashtable1[key]) - float(hashtable2[key])) / float(hashtable2[key]) * 100
    return diff

# a function that takes as input 2 identifiers
# it calls parse_all on the first identifier
# it calls parse_all on the second identifier
# it calls diff_hashtables on the two resulting hashtables
# it returns the resulting hashtable
def diff(identifier1, identifier2):
    real_times1, user_times1, space1 = parse_all(identifier1)
    real_times2, user_times2, space2 = parse_all(identifier2)
    real_times_diff = diff_hashtables(real_times1, real_times2)
    user_times_diff = diff_hashtables(user_times1, user_times2)
    space_diff = diff_hashtables(space1, space2)
    return real_times_diff, user_times_diff, space_diff

# a function that takes as input two identifiers
# it calls diff on the two identifiers
# it plots 3 scatter plots for the the resulting hashtables and saves them to files
def plot_diff(identifier1, identifier2):
    real_times_diff, user_times_diff, space_diff = diff(identifier1, identifier2)
    plt.scatter(real_times_diff.keys(), real_times_diff.values())
    plt.xlabel("filename")
    plt.ylabel("real time difference (%)")
    plt.savefig("real_times_diff_{}_{}.png".format(identifier1, identifier2))
    plt.clf()
    plt.scatter(user_times_diff.keys(), user_times_diff.values())
    plt.xlabel("filename")
    plt.ylabel("user time difference (%)")
    plt.savefig("user_times_diff_{}_{}.png".format(identifier1, identifier2))
    plt.clf()
    plt.scatter(space_diff.keys(), space_diff.values())
    plt.xlabel("filename")
    plt.ylabel("space difference (%)")
    plt.savefig("space_diff_{}_{}.png".format(identifier1, identifier2))
    plt.clf()

# a function that reads two identifiers from the command line
# it calls plot_diff on the two identifiers
if __name__ == "__main__":
    identifier1 = sys.argv[1]
    identifier2 = sys.argv[2]
    plot_diff(identifier1, identifier2)
