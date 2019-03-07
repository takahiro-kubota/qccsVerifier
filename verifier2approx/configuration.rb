class Configuration
  def initialize(proc = nil, env = nil)
    @proc = proc
    @env  = env
  end
  attr_accessor :proc, :env
  
  public
  def copy
    Configuration.new(@proc.copy, @env.copy)
  end

  def eliminate_op!
    def __eliminate_op_inter!(proc)
      ret = [] # of EnvNode with kind = "oper"
      while proc.node.kind == "oper"
        head = proc.eliminate_head!
        new_op = Environment::EnvNode.new(head.name, head.target)
        ret << new_op
      end      
      if proc.node.kind == "palla"
        ret += __eliminate_op_inter!(proc.left)
        ret += __eliminate_op_inter!(proc.right)
      elsif proc.node.kind == "restriction"
        ret += __eliminate_op_inter!(proc.left)
      end

      ret
    end # def __eliminate_op_inter!

    new_ops = __eliminate_op_inter!(@proc)
    new_ops.each { |new_op_i|
      @env.ops.unshift(new_op_i)
    }
  end # def eliminate_op!
end
