with open("lockserv.txt", "r") as f:
    content = f.read().split("DECLARE_STATES")[1]
    variables, content = content.split("BEGIN_VARLABELS")
    variables = variables.strip().split("\n")
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


    R = set()
    for line in pla:
        # print(line)
        s = ""
        for i in range(len(labels.keys())):
            label = labels[i]
            if label[:2] == "__":
                # print(i, label, line[i])
                used_labels.add((i, label))
                s += line[i]
        # print(s)
        R.add(s)

# print("\nPLA")
for i, a in enumerate(sorted(used_labels)):
    print(i, a[1])
# print("\nR")
for line in R:
    print(line)




        