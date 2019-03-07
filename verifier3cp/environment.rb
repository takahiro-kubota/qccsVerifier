require "mylib"

class Environment
  # common for ops and syms.
  # measure q, r
  # EPR qA, qB ...
  class EnvNode
    def initialize(name = nil, target = nil)
      @name = name # String
      @target = target # of qvars
    end
    attr_accessor :name, :target

    public
    def ==(other)
      @name == other.name and 
        @target == other.target
    end # ==

    def <=>(other)
      if (by_name = @name <=> other.name) == 0
        @target <=> other.target
      else
        by_name
      end
    end

    def copy
      ret = EnvNode.new(@name, @target.clone)
      ret
    end

    def print
      p [@name, @target]
    end
  end #class EnvNode

  def initialize
    @ops = []  # of EnvNode, order is significant
    @syms = [] # of EnvNode, assumed sorted
  end
  attr_accessor :ops, :syms

  def ==(other)
    envA = self.copy
    envB = other.copy

    opsA = envA.ops
    opsB = envB.ops
    symsA = envA.syms
    symsB = envB.syms

    unless symsA == symsB
      # print "\n A"
      # symsA.each { |sym_i|
      #   sym_i.print
      # }
      # print "\n B"
      # symsB.each { |sym_i|
      #   sym_i.print
      # }
      # p "symbol not equal"
      return false
    end

    j = 0
    opsA.each { |opA_i|
      if j >= opsB.length
        break
      elsif opsB[j] == opA_i
        opsB.delete_at(j)
        j = 0
      elsif disjoint?(opsB[j].target, opA_i.target)
        j += 1
        redo
      else
        return false
      end
    } #opsA.each

    return opsB == []
  end #==

  def copy
    ret = Environment.new
    @ops.each { |op_i|
      ret.ops << op_i.copy
    }
    @syms.each { |sym_i|
      ret.syms << sym_i.copy
    }
    ret
  end #copy

  def add_head!(op)
    @ops.unshift(op)
  end # add_head!

  def qv
    ret = Array.new
    @syms.each { |sym_i| 
      ret |= sym_i.target
    }
    ret
  end #qv

  def ptr(qvars)
    ret = self.copy

    delete_qvars = qvars # delete_qvars initialized
    ret.ops.length.times { |i|
      if ret.ops[i].name == "proj0" || ret.ops[i].name == "proj1" || ret.ops[i].name[0..1] == "*E"
        delete_qvars -= ret.ops[i].target
      elsif ret.ops[i].target - delete_qvars == []
        ret.ops[i] = nil
      else
        delete_qvars -= ret.ops[i].target
      end
    } 
    ret.ops.compact!

    deleted = [] # deleted initialized
    ret.syms.length.times { |i|
      if ret.syms[i].target - delete_qvars == []
        deleted |= ret.syms[i].target
        ret.syms[i] = nil
      end
    }
    ret.syms.compact!

    ptr_qvars = qvars - deleted
    ptr_node = EnvNode.new("Tr", ptr_qvars)
    # p " "
    # ret.show
    # ptr_node.print #
    # p " "
    ret.ops.unshift(ptr_node)

    ret
  end #end def ptr

  def applicable?(lhs)
    if lhs.ops == []
      j = nil
    elsif lhs.ops[0].name == "Tr"
      if @ops != [] and @ops[0].name == "Tr" and lhs.ops[0].target - @ops[0].target == []
        j = 0
      else
        return false
      end
    elsif (j = @ops.index(lhs.ops[0])) == nil
      return false
    end # if lhs.ops == []

    lhs_qv = []
    lhs.ops.each { |op_i|
      if j >= @ops.length
        return false
        # break
      elsif op_i == @ops[j] or op_i.name == "Tr"
        j += 1
        lhs_qv |= op_i.target
      elsif disjoint?(@ops[j].target, lhs_qv)
        j += 1
        redo
      else
        return false
      end
    }

    lhs.syms.each { |lhs_sym_i|
      if lhs_sym_i.name == "__"
        lhs_qv -= lhs_sym_i.target
      elsif @syms.index(lhs_sym_i) == nil
        return false
      end
    }
    
    unless j == nil
      j += 1
      for k in j .. @ops.length - 1
        unless disjoint?(@ops[k].target, lhs_qv)
          return false
        end
      end
    end

    return true
  end # def applicable?
  
  # equations : Array of equation
  def normalize!(equations)
    equations.each { |name_i, eq_i|
      if self.applicable?(eq_i.lhs)
        eq_i.counter += 1
        # p "#{name_i} is applicable." #
        # self.show
        # eq_i.lhs.show
        if eq_i.lhs.ops == []
          insert_p = nil
        else
          insert_p = @ops.index(eq_i.lhs.ops[-1])
          if insert_p != nil 
            insert_p += 1
          else
            insert_p = @ops.length
          end
        end
        eq_i.lhs.ops.each { |op_m|
          unless op_m.name == "Tr"
            @ops.delete_at(@ops.index(op_m))
            insert_p -= 1
          end
        }

        unless insert_p == nil
          insert_ops = eq_i.rhs.ops.clone
          insert_ops.each { |iop_m|
            if iop_m.name == "Tr"
              insert_ops.delete(iop_m)
            end
          }
          @ops.insert(insert_p, insert_ops)
          @ops.flatten!
        end

        eq_i.lhs.syms.each { |lhs_syms_j|
          if lhs_syms_j.name == "__"
            if eq_i.rhs.syms.index(lhs_syms_j)
              @syms.delete(lhs_syms_j)
            else
              # do nothing
            end
          else
            @syms.delete(lhs_syms_j)
          end
        }

        eq_i.rhs.syms.each { |rhs_syms_j|
          if rhs_syms_j.name == "__"
            # do nothing
          else
            @syms << rhs_syms_j
          end
        }
        @syms.sort!
      else
        # p "#{name_i} is not applicable."
      end # if self.applicable?(eq_i)
    } # equations.each
  end # def normalize!

  def show
    depth = 0
    @ops.each { |op_i|
      print " " * depth + "e|-"
      op_i.print
      depth += 1
    }
    @syms.each { |sym_i|
      print " " * depth + "e|-"
      sym_i.print
    }
  end
end #class Environment
