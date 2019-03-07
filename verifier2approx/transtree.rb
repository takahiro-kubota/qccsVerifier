require "transition"

class TransTreeGenerator
  include Transition

  class TransTreeNode
    def initialize(node = nil, succ = [])
      @node = node # TransNode
      @succ = succ # Array of TransTreeNode
    end
    attr_accessor :node, :succ
  end

  def initialize
    @trans_tree = nil
    @total_transnum = 0
    @total_pathnum = 0
  end

  private
  def __gen_transtree_inter(cfg)
    ret = [] # Array of TransTreeNode
    trans = strong_reduction(cfg)
    trans.each { |trans_i|
      ret << TransTreeNode.new(trans_i, __gen_transtree_inter(trans_i.cfg))
    }
    
    ret
  end

  def __show_tree_inter(treenode, depth)
    @total_transnum += 1
    margin = " " * depth

    print margin, "t|-"
    treenode.node.label.print

    treenode.succ.each { |succ_i|
      __show_tree_inter(succ_i, depth + 1)
    }
    if treenode.succ == []
      @total_pathnum += 1
    end
  end

  public
  def gen_transtree(cfg)
    rootlabel = Label.new
    root = TransNode.new(rootlabel, cfg)
    succ = __gen_transtree_inter(cfg)
    @trans_tree = TransTreeNode.new(root, succ)
  end

  def show_tree 
    __show_tree_inter(@trans_tree, 0)
    print "transnum: ", @total_transnum, "\n"
    print "pathnum: ", @total_pathnum, "\n"
  end
end # class TransTree
