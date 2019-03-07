require "transition"

class Bisimulation
  include Transition

  def initialize(cfgA, cfgB, equations, opt_hash = nil)
    @counter = 0
    @true_counter = 0
    @history_true = 0
    @history_false = 0
    @weak_counter = 0

    @history = Hash.new # H[cfgX, cfgY] = true

    @adv_op_num = 0

    @cfgA = cfgA
    @cfgB = cfgB
    @equations = equations
    @opt_hash = opt_hash
  end # class Bisimulation

  private
  def __weak_reduction(cfg)
    ret = [] # of TransNode
    
    tau_star(cfg).each { |cfg_i|
      ret << TransNode.new(Label.new("tau", nil, nil), cfg_i)
      strong_reduction(cfg_i).each { |trans_i|
        if trans_i.label.kind == "tau"
          # do nothing
        else
          tau_star(trans_i.cfg).each  { |weak_i|
            ret << TransNode.new(trans_i.label, weak_i)
          }
        end
      }
    }
    
    ret
  end # def __weak_reduction(cfg)

  private
  def __weak_reduction_if(cfg)
    ret = [] # of a pair of TransNode
    
    tau_star(cfg).each { |cfg_i|
      strong_reduction(cfg_i).each { |trans_i|
        if trans_i.label.kind != "if" or trans_i.label.name != "proj1"
          # do nothing
        else
          tau_star(trans_i.cfg).each  { |weak_i|
            ret_component = []
            tt_label = trans_i.label
            tt_cfg   = weak_i
            strong_reduction(cfg_i).each{ |trans_k|
              if trans_k.label.kind == "if" and trans_k.label.name == "proj0"
                tau_star(trans_k.cfg).each { |weak_m|
                  ff_label = trans_k.label
                  ff_cfg   = weak_m
                  ret_component[0] = TransNode.new(tt_label, tt_cfg)
                  ret_component[1] = TransNode.new(ff_label, ff_cfg)
                  ret << ret_component
                }
                break
              end
            }
          }
        end
      }
    }
    
    ret
  end # def __weak_reduction(cfg)

  def __judge_inter(arg_cfgA, arg_cfgB)
    cfgA = arg_cfgA.copy
    cfgB = arg_cfgB.copy

    @counter += 1
    if @counter % 100 == 0
      print @counter, "...\n"
    end

    cfgA.eliminate_op!
    cfgB.eliminate_op!

    ## check qv
    qvA = cfgA.proc.qv.sort
    qvB = cfgB.proc.qv.sort

    unless qvA == qvB
      if @opt_hash[:d]
        puts "qvA and qvB are not equal."
        puts "qvA: #{qvA}"
        puts "qvB: #{qvB}"
        puts "A's process: "
        cfgA.proc.show_tree
        puts "B's process: "
        cfgB.proc.show_tree
      end
      return false
    end

    qvbarA = cfgA.env.qv - qvA

    cfgA.env.normalize!(@equations)
    cfgB.env.normalize!(@equations)

    envA_ptr = cfgA.env.ptr(qvA)
    envB_ptr = cfgB.env.ptr(qvB)

    envA_ptr.normalize!(@equations)
    envB_ptr.normalize!(@equations)

    envA_view = envA_ptr.ptr(qvA)
    envB_view = envB_ptr.ptr(qvB)

    if @opt_hash[:v]
      puts "A's process: "
      cfgA.proc.show_tree
      puts "A's env. after trace out: "
      envA_view.show
      puts "B's process: "
      cfgB.proc.show_tree
      puts "B's env. after trace out: "
      envB_view.show
    end
    
    unless envA_view == envB_view
      if @opt_hash[:v] == nil
        if @opt_hash[:p]
          puts "A's process: "
          cfgA.proc.show_tree
          puts "B's process: "
          cfgB.proc.show_tree
        end
        if @opt_hash[:e]
          puts "A's environment: "
          cfgA.env.show
          puts "B's environment: "
          cfgB.env.show
        end
        if @opt_hash[:u]
          puts "A's env. after trace out: "
          envA_view.show
          puts "B's env. after trace out: "
          envB_view.show
        end
        if @opt_hash[:d]
          puts "Partial traces are not equal."
          puts "A's process: "
          cfgA.proc.show_tree
          puts "B's process: "
          cfgB.proc.show_tree
          puts "A's environment: "
          cfgA.env.show
          puts "B's environment: "
          cfgB.env.show
          puts "A's env. after trace out: "
          envA_view.show
          puts "B's env. after trace out: "
          envB_view.show
        end
      end

      return false
    end

    #add adversarial computation
    if cfgA.env.ops == [] or
        cfgA.env.ops[0].name[0..1] != "*E" or
        qvbarA - cfgA.env.ops[0].target != []
      adv_op = Environment::EnvNode.new("*E" + @adv_op_num.to_s, qvbarA)
      cfgA.env.add_head!(adv_op)
      cfgB.env.add_head!(adv_op.copy)
      @adv_op_num += 1
    end

    strongsA = strong_reduction(cfgA)
    strongsB = strong_reduction(cfgB)
    weaksA = __weak_reduction(cfgA)
    weaksB = __weak_reduction(cfgB)

    # check B sims A.
    if strongsA != []
      strongsA.each{ |strongsA_i|
        lblA_i = strongsA_i.label
        cfgA_i = strongsA_i.cfg
        flag_found_B = false
        same_label_exists_uptotau_B = false
        strongsB.each{ |strongsB_j|
          lblB_j = strongsB_j.label
          cfgB_j = strongsB_j.cfg
          if lblA_i == lblB_j
            same_label_exists_uptotau_B = true
            if  __judge_inter(cfgA_i, cfgB_j) == true
              @history[[cfgA_i, cfgB_j]] = true
              flag_found_B = true
              break
            else
              @history[[cfgA_i, cfgB_j]] = false
            end
          end
        } # strongsB.each 
        if flag_found_B == false and lblA_i.kind != "if"
          weaksB.each{ |weakB_j|
            wlblB_j = weakB_j.label
            wcfgB_j = weakB_j.cfg
            if lblA_i == wlblB_j
              same_label_exists_uptotau_B = true
              if  __judge_inter(cfgA_i, wcfgB_j) == true
                @weak_counter += 1
                flag_found_B = true
                break
              end
            end
          } # weaksB.each
        elsif flag_found_B == false and lblA_i.kind == "if" and lblA_i.name == "proj1"
          weaksifB = __weak_reduction_if(cfgB)
          cfgA_true = cfgA_i
          strongsA.each { |strongsA_k|
            label_k = strongsA_k.label
            cfg_k = strongsA_k.cfg
            if label_k.kind == "if" and label_k.name == "proj0" and label_k.target == lblA_i.target
              cfgA_false = cfg_k
              break
              end
          }
          weaksifB.each{ |weakifB_j|
            wcfgB_j_true = weakifB_j[0]
            wcfgB_j_false = weakifB_j[1]
            if __judge_inter(cfgA_true, wcfgB_j_true) == true and  __judge_inter(cfgA_false, wcfgB_j_false) == true                
              @weak_counter += 1
              flag_found_B = true
            end
          }
        end
        if flag_found_B == false
          if @opt_hash[:d] and 
              @opt_hash[:v] == nil and
              same_label_exists_uptotau_B == false
            print "B does not have the transition: "
            lblA_i.print
            puts "A's process: "
            cfgA.proc.show_tree
            puts "B's process: "
            cfgB.proc.show_tree
          end
          return false
        end
      }
    end # if strongsA != []
    # check B sims A ends here.
    
    # check A sims B.
    if strongsB != []
      strongsB.each{ |strongsB_i|
        lblB_i = strongsB_i.label
        cfgB_i = strongsB_i.cfg
        flag_found_A = false
        same_label_exists_uptotau_A = false
        strongsA.each{ |strongsA_j|
          lblA_j = strongsA_j.label
          cfgA_j = strongsA_j.cfg
          if lblB_i == lblA_j
            same_label_exists_uptotau_A = true
            if (h = @history[[cfgA_j, cfgB_i]]) != nil
              if h == true
                @history_true += 1
                flag_found_A = true
                break
              else
                @history_false += 1
                next
              end
            elsif __judge_inter(cfgA_j, cfgB_i) == true
              flag_found_A = true
              break
            end
          end
        } # strongA.each
        if flag_found_A == false and lblB_i.kind != "if"
          weaksA.each{ |weaksA_j|
            wlblA_j = weaksA_j.label
            wcfgA_j = weaksA_j.cfg
            if lblB_i == wlblA_j
              same_label_exists_uptotau_A = true
              if  __judge_inter(wcfgA_j, cfgB_i) == true
                @weak_counter += 1
                flag_found_A = true
                break
              end
            end
          } # weaksA.each
        elsif flag_found_A == false and lblB_i.kind == "if" and lblA_i.name == "proj1"
          weaksifA = __weak_reduction_if(cfgA)
          cfgB_true = cfgB_i
          strongsB.each { |strongsB_k|
            label_k = strongsB_k.label
            cfg_k = strongsB_k.cfg
            if label_k.kind == "if" and label_k.name == "proj0" and label_k.target == lblB_i.target
              cfgB_false = cfg_k
              break
            end
          }
          weaksifA.each{ |weakifA_j|
            wcfgA_j_true = weakifA_j[0]
            wcfgA_j_false = weakifA_j[1]
            if __judge_inter(cfgB_true, wcfgA_j_true) == true and  __judge_inter(cfgB_false, wcfgA_j_false) == true                
              @weak_counter += 1
              flag_found_A = true
            end
          }
        end
        if flag_found_A == false
          if @opt_hash[:d] and
              @opt_hash[:v] == nil and
              same_label_exists_uptotau_A == false
            print "A does not have the transition: "
            lblB_i.print
            puts "A's process: "
            cfgA.proc.show_tree
            puts "B's process: "
            cfgB.proc.show_tree
          end
          return false
        end
      }
    end
    # check A sims B ends here.

    # if strongsB == [] and strongsA == []
    #   p "good job"
    # end

    @true_counter += 1

    return true
  end # def __judge_inter
  
  public
  def judge
    judge_result = __judge_inter(@cfgA, @cfgB)

    print "\n"
    @equations.each { |name_i, eq_i|
      print "equation #{name_i} : #{eq_i.counter} \n"
    }
    if judge_result == true
      print "\n bisimilar.\n\n"
    else
      print "\nverfication failed.\n\n"
    end

    print "counter = "
    p @counter
    print "true_counter = "
    p @true_counter
    print "history size = "
    p @history.size
    print "history hit = "
    p (@history_true + @history_false)
    print "weak = "
    p @weak_counter
  end # def judge
end # class Bisimulation
