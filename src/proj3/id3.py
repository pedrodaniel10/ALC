#!/usr/bin/env python3
# This file was originally from https://github.com/tofti/python-id3-trees
# Last modified by Pedro Lopes at Fri Nov 15 11:07:00 WEST 2019
import sys
import math
import os


def get_uniq_values(data):
    idx_to_name = data['idx_to_name']
    idxs = idx_to_name.keys()

    val_map = {}
    for idx in iter(idxs):
        val_map[idx_to_name[idx]] = set()

    for data_row in data['rows']:
        for idx in idx_to_name.keys():
            att_name = idx_to_name[idx]
            val = data_row[idx]
            if val not in val_map.keys():
                val_map[att_name].add(val)
    return val_map


def get_class_labels(data, target_attribute):
    rows = data['rows']
    col_idx = data['name_to_idx'][target_attribute]
    labels = {}
    for r in rows:
        val = r[col_idx]
        if val in labels:
            labels[val] = labels[val] + 1
        else:
            labels[val] = 1
    return labels


def entropy(n, labels):
    ent = 0
    for label in labels.keys():
        p_x = labels[label] / n
        ent += - p_x * math.log(p_x, 2)
    return ent


def partition_data(data, group_att):
    partitions = {}
    data_rows = data['rows']
    partition_att_idx = data['name_to_idx'][group_att]
    for row in data_rows:
        row_val = row[partition_att_idx]
        if row_val not in partitions.keys():
            partitions[row_val] = {
                'name_to_idx': data['name_to_idx'],
                'idx_to_name': data['idx_to_name'],
                'rows': list()
            }
        partitions[row_val]['rows'].append(row)
    return partitions


def avg_entropy_w_partitions(data, splitting_att, target_attribute):
    # find uniq values of splitting att
    data_rows = data['rows']
    n = len(data_rows)
    partitions = partition_data(data, splitting_att)

    avg_ent = 0

    for partition_key in partitions.keys():
        partitioned_data = partitions[partition_key]
        partition_n = len(partitioned_data['rows'])
        partition_labels = get_class_labels(partitioned_data, target_attribute)
        partition_entropy = entropy(partition_n, partition_labels)
        avg_ent += partition_n / n * partition_entropy

    return avg_ent, partitions


def most_common_label(labels):
    mcl = max(labels, key=lambda k: labels[k])
    return mcl


def id3(data, uniqs, remaining_atts, target_attribute):
    labels = get_class_labels(data, target_attribute)

    node = {}

    if len(labels.keys()) == 1:
        node['label'] = next(iter(labels.keys()))
        return node

    if len(remaining_atts) == 0:
        node['label'] = most_common_label(labels)
        return node

    n = len(data['rows'])
    ent = entropy(n, labels)

    max_info_gain = None
    max_info_gain_att = None
    max_info_gain_partitions = None

    for remaining_att in remaining_atts:
        avg_ent, partitions = avg_entropy_w_partitions(
            data, remaining_att, target_attribute)
        info_gain = ent - avg_ent
        if max_info_gain is None or info_gain > max_info_gain:
            max_info_gain = info_gain
            max_info_gain_att = remaining_att
            max_info_gain_partitions = partitions

    if max_info_gain is None:
        node['label'] = most_common_label(labels)
        return node

    node['attribute'] = max_info_gain_att
    node['nodes'] = {}

    remaining_atts_for_subtrees = set(remaining_atts)
    remaining_atts_for_subtrees.discard(max_info_gain_att)

    uniq_att_values = uniqs[max_info_gain_att]

    for att_value in uniq_att_values:
        if att_value not in max_info_gain_partitions.keys():
            node['nodes'][att_value] = {'label': most_common_label(labels)}
            continue
        partition = max_info_gain_partitions[att_value]
        node['nodes'][att_value] = id3(
            partition, uniqs, remaining_atts_for_subtrees, target_attribute)

    return node


def get_number_nodes(node):
    if 'label' in node:
        return 1
    elif 'attribute' in node:
        sum = 1
        if len(node['nodes']) != 2:
            sum = 0

        for subnode_key in node['nodes']:
            sum += get_number_nodes(node['nodes'][subnode_key])
        return sum


def get_model_id3(root):
    def prune(node):
        if 'label' in node:
            return node
        elif 'attribute' in node:
            if len(node['nodes']) == 1:
                return prune(node['nodes'][0])
            elif len(node['nodes']) == 2:
                node['nodes'][0] = prune(node['nodes'][0])
                node['nodes'][1] = prune(node['nodes'][1])
                return node
    root = prune(root)

    queue = []
    queue.append(root)
    id = 1

    while len(queue) != 0:
        node = queue.pop(0)
        node['id'] = id
        id += 1
        if "label" in node:
            continue
        for subnode_key in node['nodes']:
            queue.append(node['nodes'][subnode_key])

    model = dict()

    def traverse(node):
        nonlocal model
        if model == None:
            return
        if 'label' in node:
            model["v[{}]".format(node['id'])] = True
            model["c[{}]".format(node['id'])] = {
                0: False, 1: True}[node['label']]
        elif 'attribute' in node:
            if (len(node['nodes']) != 2):
                model = None
                return
            model["v[{}]".format(node['id'])] = False
            model["l[{},{}]".format(node['id'], node['nodes'][0]['id'])] = True
            model["r[{},{}]".format(node['id'], node['nodes'][1]['id'])] = True
            model["a[{},{}]".format(node['attribute'], node['id'])] = True
            for subnode_key in node['nodes']:
                traverse(node['nodes'][subnode_key])
    traverse(root)
    return model


def run_id3(samples, k):
    data = dict()
    data['header'] = ["{}".format(i)
                      for i in range(1, k+1)] + ['Classification']
    data['rows'] = samples
    name_to_idx = dict()
    idx_to_name = dict()
    for i in range(len(data['header'])):
        name_to_idx[data['header'][i]] = i
        idx_to_name[i] = data['header'][i]
    data['name_to_idx'] = name_to_idx
    data['idx_to_name'] = idx_to_name

    target_attribute = "Classification"
    remaining_attributes = set(data['header'])
    remaining_attributes.remove(target_attribute)

    uniqs = get_uniq_values(data)

    return id3(data, uniqs, remaining_attributes, target_attribute)
