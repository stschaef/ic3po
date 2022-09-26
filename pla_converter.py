import sys

def dont_care_assignments(in_set, out_set):
    new_in_set = set()
    change = False
    for string in in_set:
        if string.count("-") == 0:
            out_set.add(string)
            continue
        change = True
        new_in_set.add(string.replace('-', '0', 1))
        new_in_set.add(string.replace('-', '1', 1))
    if not change:
        return
    dont_care_assignments(new_in_set, out_set)


with open(sys.argv[1], "r") as f:
    content = f.read()
    if len(content.split("\n")) < 4:
        print("Error generating raw data\naborting PLA generation")
        exit()
    content = content.split("BEGIN_VARLABELS")[1]
    if content.split("\n")[-2].strip() == "-- Finite check: violated --":
        print("Finite check: violated\naborting PLA generation")
        exit()
    _labels, _pla = content.strip().split("END_VARLABELS")
    _labels = _labels.strip().split("\n")
    labels = {}
    for _label in _labels:
        labels[int(_label.split("\t")[0])] = _label.split("\t")[1]
    
    _pla = _pla.strip().split("\n")
    pla = []
    for line in _pla:
        pla.append(line.strip().split(" ")[0])

    # print("VARS")
    # for var in variables:
    #     print(var)
    # print(labels)
    # print("\nLABELS")
    # for idx, label in labels.items():
    #     print(idx, label)

    used_labels = set()
    print(labels)

    R = set()
    for line in pla:
        # print(line)
        s = ""
        for i in range(len(labels.keys())):
            label = labels[i]
            if ("__" + label) in labels.values() or label[:3] == "en_" or label[0] == "(":
                continue
            else:
            # if label[:2] == "__":
                # print(i, label, line[i])
                used_labels.add((i, label))
                s += line[i]
        # print(s)
        R.add(s)
        # minterms = set()
        # dont_care_assignments(set([s]), minterms)
        # R.update(minterms)
        # print("R", R)


print(f".i {len(used_labels)}")
print(f".o 1")
label_str = ".ilb"
# print("\nPLA")
for a in sorted(used_labels):
    label_str += f" {a[1]}"
print(label_str)
print(".ob out")
# print("\nR")
for line in R:
    print(line + " 1")




        