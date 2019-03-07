require "mylib.rb"

class QProcess
  class ProcessNode
    def initialize(kind = nil, name = nil, target = [])
      @kind = kind # "discard", "send", "receive", "oper",
                  # "palla", "restriction"
      @name = name # name of channel or oper, String
      @target = target # Array of qvar or channel (if restriction)
    end
    attr_accessor :kind, :name, :target

    public
    def copy
      ret = ProcessNode.new
      ret.kind = @kind
      ret.name = @name
      ret.target = @target.clone
      ret
    end

    def print
      p [@kind, @name, @target]
    end
  end #ProcessNode

  def initialize
    @node = nil #ProcessNode
    @left = nil #QProcess
    @right = nil #QProcess
  end
  attr_accessor :node, :left, :right

  public
  def qv #with checking unique ownership
    ret = []
    qv_left = []
    qv_right = []
    
    if @left != nil
      qv_left = @left.qv
    end
    if @right != nil
      qv_right = @right.qv
    end

    ret |= qv_left
    ret |= qv_right

    kind = @node.kind
    case kind
    when "discard"
      ret |= @node.target
    when "send"
      unless disjoint?(@node.target, qv_left)
        raise "send, unique ownership is broken."
      end
      ret |= @node.target
    when "receive"
      ret.delete(@node.target[0])
    when "oper"
      ret |= @node.target
    when "palla"
      unless disjoint?(qv_left, qv_right)
        raise "palla, unique ownership is broken."
      end
    when "condition"
      ret |= @node.target
    end #case
    
    ret
  end #qv

  def subst!(src, dst)
    unless @left == nil
      @left.subst!(src, dst)
    end
    unless @right == nil
      @right.subst!(src, dst)
    end

    kind = @node.kind
    if ["discard", "send", "oper", "condition"].index(kind)
      index = @node.target.index(dst)
      if index
        @node.target[index] = src
      end
    end
  end #subst

  def eliminate_head!
    ret = @node.copy
    if @node.kind == "palla"
      p "palla cannot be eliminated."
    elsif @left == nil
      p "process node cannot be eliminated 
         bcs it has no child"
    end
    self.node = @left.node
    self.left = @left.left

    ret
  end

  def copy
    ret = QProcess.new
    ret.node = @node.copy
    unless @left == nil
      ret.left = @left.copy
    end
    unless @right == nil
      ret.right = @right.copy
    end

    ret
  end

  def show_tree
    def __show_tree_inter(depth, proc_tree)
      print " " * depth + "p|-"
      proc_tree.node.print
      if proc_tree.left
        __show_tree_inter(depth + 1, proc_tree.left)
      end
      if proc_tree.right
        __show_tree_inter(depth + 1, proc_tree.right)
      end
    end
    __show_tree_inter(0, self)
  end

end #QProcess
