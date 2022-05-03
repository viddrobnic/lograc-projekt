from typing import Optional


from enum import Enum


class Direction(Enum):
    LEFT = 1
    MIDDLE = 2
    RIGHT = 3


class Node:
    def __init__(self) -> None:
        self.left: Optional[Node] = None
        self.right: Optional[Node] = None
        self.middle: Optional[Node] = None

        self.data_1 = None
        self.data_2 = None

    def _to_str(self, indent=0):
        left = 'None' if self.left is None else self.left._to_str(indent + 1)
        middle = 'None' if self.middle is None else self.middle._to_str(
            indent + 1)
        right = 'None' if self.right is None else self.right._to_str(
            indent + 1)

        res = f'{" "*indent}Data_1: {self.data_1}, Data_2: {self.data_2}\n'
        res += f'{" "*indent}  - Left: {left}\n'
        res += f'{" "*indent}  - Middle: {middle}\n'
        res += f'{" "*indent}  - Right: {right}'

        return res

    def _assign(self, node: 'Node'):
        self.data_1 = node.data_1
        self.data_2 = node.data_2
        self.left = node.left
        self.right = node.right
        self.middle = node.middle

    def __str__(self) -> str:
        return self._to_str()

    def is_two_node(self) -> bool:
        return self.data_1 is not None and self.data_2 is None

    def insert(self, val) -> bool:
        if self.data_1 is None:
            self.data_1 = val
            self.left = Node()
            self.right = Node()
            return True

        if self.data_2 is None:  # 2-node
            if val < self.data_1:
                if self.left.insert(val):
                    self.merge(Direction.LEFT)

                return False
            elif val > self.data_1:
                if self.right.insert(val):
                    self.merge(Direction.RIGHT)

                return False
        else:  # 3-node
            if val < self.data_1:
                if self.left.insert(val):
                    self.merge(Direction.LEFT)
                    return True

                return False
            elif val > self.data_1 and val < self.data_2:
                if self.middle.insert(val):
                    self.merge(Direction.MIDDLE)
                    return True

                return False
            elif val > self.data_2:
                if self.right.insert(val):
                    self.merge(Direction.RIGHT)
                    return True

                return False

        return False

    def merge(self, direction: Direction):
        if self.is_two_node():  # 2-node
            if direction == Direction.LEFT:
                if not self.left.is_two_node():
                    raise Exception(
                        f'Invalid node state: left node is not a 2-node')

                self.data_2 = self.data_1
                self.data_1 = self.left.data_1
                self.middle = self.left.right
                self.left = self.left.left
            elif direction == Direction.RIGHT:
                if not self.right.is_two_node():
                    raise Exception(
                        f'Invalid node state: right node is not a 2-node')

                self.data_2 = self.right.data_1
                self.middle = self.right.left
                self.right = self.right.right
            else:
                raise Exception(f'Invalid direction: {direction}')
        elif self.data_1 is not None and self.data_2 is not None:  # 3-node
            if direction == Direction.LEFT:
                if not self.left.is_two_node():
                    raise Exception(
                        f'Invalid node state: left node is not a 2-node')

                new_node = Node()
                new_node.data_1 = self.data_1
                new_node.left = self.left

                new_node.right = Node()
                new_node.right.data_1 = self.data_2
                new_node.right.left = self.middle
                new_node.right.right = self.right

                self._assign(new_node)
            elif direction == Direction.MIDDLE:
                if not self.middle.is_two_node():
                    raise Exception(
                        f'Invalid node state: middle node is not a 2-node')

                new_node = Node()
                new_node.data_1 = self.middle.data_1

                new_node.left = Node()
                new_node.left.data_1 = self.data_1
                new_node.left.left = self.left
                new_node.left.right = self.middle.left

                new_node.right = Node()
                new_node.right.data_1 = self.data_2
                new_node.right.left = self.middle.right
                new_node.right.right = self.right

                self._assign(new_node)
            else:
                if not self.right.is_two_node():
                    raise Exception(
                        f'Invalid node state: right node is not a 2-node')
                new_node = Node()
                new_node.data_1 = self.data_2
                new_node.right = self.right

                new_node.left = Node()
                new_node.left.data_1 = self.data_1
                new_node.left.left = self.left
                new_node.left.right = self.middle

                self._assign(new_node)
        else:
            raise Exception(
                f'Invalid node state. Data_1: {self.data_1}, Data_2: {self.data_2}')

    def search(self, val) -> bool:
        if self.data_1 is None:
            return False

        if self.data_2 is None:  # 2-node
            if val == self.data_1:
                return True
            elif val < self.data_1:
                return self.left.search(val)
            else:
                return self.right.search(val)
        else:  # 3-node
            if val == self.data_1 or val == self.data_2:
                return True
            elif val < self.data_1:
                return self.left.search(val)
            elif val > self.data_1 and val < self.data_2:
                return self.middle.search(val)
            else:
                return self.right.search(val)

    def height(self) -> int:
        if self.data_1 is None:
            return 0

        if self.data_2 is None:  # 2-node
            return 1 + max(self.left.height(), self.right.height())
        else:  # 3-node
            return 1 + max(self.left.height(), self.middle.height(), self.right.height())

    def balanced(self) -> bool:
        if self.data_1 is None:
            return True

        if self.data_2 is None:
            return self.left.balanced() and self.right.balanced() and self.left.height() == self.right.height()
        else:
            return self.left.balanced() and self.middle.balanced() and self.right.balanced() and self.left.height() == self.right.height() and self.left.height() == self.middle.height()


tree = Node()
for i in range(1000):
    assert not tree.search(i)
    tree.insert(i)
    assert tree.search(i)
    assert tree.balanced()

# print(tree)
