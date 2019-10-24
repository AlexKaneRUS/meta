with open('tm_third_compiler.txt', 'r') as f1, open('tm_second_compiler.txt',
                                                    'r') as f2:
    for l1, l2 in zip(f1.readlines(), f2.readlines()):
        assert l1 == l2

with open('fc_third_compiler.txt', 'r') as f1, open('fc_second_compiler.txt',
                                                    'r') as f2:
    for l1, l2 in zip(f1.readlines(), f2.readlines()):
        assert l1 == l2
