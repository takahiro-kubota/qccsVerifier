require "mylib"
require "eqparser"

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
        # p opA_i.name
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

  # re-orders ops so that it's understood which ops are matched as __
  def applicable?(eqation)
    lhs = eqation.lhs
    rhs = eqation.rhs
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
    i = 0
    lhs.ops.each { |op_i|
      if op_i.name == "__"
        l = j # current position
        wild_alive = op_i.target # alive target
        wild_matched = [] # Array of ops
        while wild_alive != [] and l < @ops.length
          if @ops[l].target - wild_alive == []
            wild_matched << @ops.delete_at(l)
          else
            wild_alive -= @ops[l].target
            l += 1
          end
        end
        number_of_wild_matched = wild_matched.length

        wild_matched_for_lhs = []
        wild_matched_for_rhs = []
        wild_matched.each { |wild_matched_i|
          wild_matched_for_lhs << wild_matched_i.copy
          wild_matched_for_rhs << wild_matched_i.copy
        }
        unless wild_matched == [] # i.e. __ works as the Identity op.
          @ops.insert(j, wild_matched)
          @ops.flatten!
          lhs_qv |= op_i.target
        end
        j += number_of_wild_matched
        lhs.ops[i] = wild_matched_for_lhs

        for i in 0 .. rhs.ops.length - 1
          if rhs.ops[i] == op_i
            rhs_wild_position = i
            break
          end
        end
        rhs.ops[rhs_wild_position] = wild_matched_for_rhs
        rhs.ops.flatten!
      else
        found = false
        # forward seek
        jf = j
        while jf < @ops.length
          if op_i == @ops[jf] or op_i.name == "Tr"
            j = jf + 1
            found = true
            lhs_qv |= op_i.target
            break
          elsif disjoint?(@ops[jf].target, lhs_qv)
            jf += 1
          else
            # op_i.print
            # @ops[jf].print
            break
          end
        end

        # backward seek
        # if found == false and i > 0 and disjoint?(op_i.target, lhs.ops[i - 1].target)
        #   backward_set = [] # set of indices
        #   jb = j - 2
        #   while jb >= 0
        #     if op_i == @ops[jb]
        #       # p "success!"
        #       # backward set's order is ookii-jun
        #       backward_set_test = true
        #       backward_set.each { |m|
        #         x = m + 1 
        #         while x < j
        #           if disjoint?(@ops[x].target, @ops[m].target) == false
        #             backward_set_test = false
        #             break
        #           end
        #         end
        #         if backward_set_test == false
        #           break
        #         end
        #       }
        #       if backward_set_test == true
        #         found = true
        #         backing = 0
        #         backward_set.each { |m|
        #           @ops.insert(j, nil)
        #           @ops[m], @ops[j] = @ops[j], @ops[m]
        #           backing += 1
        #         }
        #         @ops.flatten!
        #         p "#{backing}: before"
        #         p "#{j}: before"
        #         j = j - backing
        #         p "#{j}: after"
        #       end
        #       break
        #     elsif disjoint?(op_i.target, @ops[jb].target)
        #       # print "dj!  #{i}"
        #       # op_i.print
        #       jb -= 1
        #     else
        #       backward_set << jb
        #       jb -= 1
        #     end
        #   end
        # end

        if found == false
          # op_i.print
          return false
        end

      end # op_i.name == "__"
      i += 1
    }
    lhs.ops.flatten! # attention!

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
      eq_i_lhs = eq_i.lhs.copy
      eq_i_rhs = eq_i.rhs.copy
      eq_i_tmp = EqParser::Equation.new
      eq_i_tmp.lhs = eq_i_lhs
      eq_i_tmp.rhs = eq_i_rhs
      if self.applicable?(eq_i_tmp)
        eq_i.counter += 1
        # p "#{name_i} is applicable."
        # self.show
        # eq_i_lhs.show
        if eq_i_lhs.ops == []
          insert_p = nil
        else
          insert_p = @ops.rindex(eq_i_lhs.ops[-1])
          # print "zenbude: " ##
          # p @ops.length  ##
          # print "1: "  ##
          # p insert_p ##
          if insert_p != nil 
            insert_p += 1
          else
            insert_p = @ops.length
          end
        end
        eq_i_lhs.ops.each { |op_m|
          unless op_m.name == "Tr"
            @ops.delete_at(@ops.index(op_m))
            insert_p -= 1
          end
        }
        # print "fin: " ##
        # p insert_p ##
        unless insert_p == nil
          insert_ops = eq_i_rhs.ops.clone
          insert_ops.each { |iop_m|
            if iop_m.name == "Tr"
              insert_ops.delete(iop_m)
            end
          }
          @ops.insert(insert_p, insert_ops)
          @ops.flatten!
        end

        eq_i_lhs.syms.each { |lhs_syms_j|
          if lhs_syms_j.name == "__"
            if eq_i_rhs.syms.index(lhs_syms_j)
              @syms.delete(lhs_syms_j)
            else
              # do nothing
            end
          else
            @syms.delete(lhs_syms_j)
          end
        }

        eq_i_rhs.syms.each { |rhs_syms_j|
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
