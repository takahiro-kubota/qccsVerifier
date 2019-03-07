# one-step transition *up to operation*

require "configuration"
require "envparser"

module Transition
  class Label # ->^a *or* =>->^a=> 's a
    def initialize(kind = nil, name = nil, target = [])
      @kind = kind
      @name = name
      @target = target
    end
    attr_accessor :kind, :name, :target

    public
    def ==(other)
      if @kind == "tau"
        return other.kind == "tau"
      else
        return @kind == other.kind && 
          @name == other.name &&
          @target == other.target
      end
    end

    def print
      p [@kind, @name, @target]
    end
  end # class Label

  class TransNode
    def initialize(label = nil, cfg = nil)
      @label = label
      @cfg = cfg
    end
    attr_accessor :label, :cfg
  end # class TransNode

  private
  def __search_receive(name, target, proc)
    ret = [] # of procs
    case proc.node.kind
    when "receive"
      if proc.node.name == name
        tmp = proc.copy
        tmp.eliminate_head!
        tmp.subst!(target[0], proc.node.target[0])
        ret << tmp
      end
    when "palla"
      tmp_procs_l =  __search_receive(name, target, proc.left)
      tmp_procs_l.each { |proc_i|
        add = proc.copy
        add.left = proc_i
        ret << add
      }
      tmp_procs_r =  __search_receive(name, target, proc.right)
      tmp_procs_r.each { |proc_i|
        add = proc.copy
        add.right = proc_i
        ret << add
      }
    else
    end

    ret
  end

  def __search_send(proc) # returns array of [ProcessNode, send-reduced proc]
    ret = []
    case proc.node.kind
    when "send"
      newproc = proc.copy
      newproc.eliminate_head!
      ret << [proc.node.copy, newproc]
    when "palla"
      tmp_procs_l = []
      tmp_procs_l =  __search_send(proc.left)
      tmp_procs_l.each { |proc_i|
        add = proc.copy
        add.left = proc_i[1];
        ret << [proc_i[0], add]
      }
      tmp_procs_r = []
      tmp_procs_r =  __search_send(proc.right)
      tmp_procs_r.each { |proc_i|
        add = proc.copy
        add.right = proc_i[1]
        ret << [proc_i[0], add]
      }
    else
      # do nothing
    end

    ret
  end

  # one-step strong reduction
  def __strong_reduction_inter(cfg, restr_ch)
    ret = [] # of TransNode

    cfg.eliminate_op!
    
    proc = cfg.proc
    env = cfg.env
    
    case proc.node.kind
    when "discard"
      #do nothing
    when "send"
      chname = proc.node.name
      unless restr_ch.include?(chname)
        newlabel = Label.new(proc.node.kind, chname, proc.node.target)
        newproc = proc.copy
        newproc.eliminate_head!
        newcfg = Configuration.new(newproc, env.copy)
        ret << TransNode.new(newlabel, newcfg)
      end
    when "receive"
      chname = proc.node.name
      unless restr_ch.include?(chname)
        newlabel = Label.new(proc.node.kind, chname, proc.node.target)
        newproc = proc.copy
        newproc.eliminate_head!
        newcfg = Configuration.new(newproc, env.copy)
        ret << TransNode.new(newlabel, newcfg)
      end
    when "palla"
      #non palla-rule trans.
      l_cfg = Configuration.new(proc.left.copy, env.copy)
      tmp_trans = __strong_reduction_inter(l_cfg, restr_ch)
      tmp_trans.each { |trans_i|
        newproc = proc.copy
        newproc.left = trans_i.cfg.proc
        newcfg = Configuration.new(newproc, trans_i.cfg.env)
        ret << TransNode.new(trans_i.label, newcfg)
      }
      r_cfg = Configuration.new(proc.right.copy, env.copy)
      tmp_trans = __strong_reduction_inter(r_cfg, restr_ch)
      tmp_trans.each { |trans_i|
        newproc = proc.copy
        newproc.right = trans_i.cfg.proc
        newcfg = Configuration.new(newproc, trans_i.cfg.env)
        ret << TransNode.new(trans_i.label, newcfg)
      }

      #tau trans.
      send_redexes = [] # of [ProcessNode, send-reduced proc]
      send_redexes = __search_send(proc)
      send_redexes.each { |redex_i|
        name = redex_i[0].name
        target  = redex_i[0].target
        proc = redex_i[1]
        tmp_procs = __search_receive(name, target, proc) # of reduced proc
        tmp_procs.each { |proc_i|
          cfg_i = Configuration.new(proc_i, env.copy)
          lebel_i = Label.new("tau", name, target)
          ret << TransNode.new(lebel_i, cfg_i)
        }
      }
      ret.reverse!
     when "condition" # 1 is "true" and 0 is "false", 
      # then 
      # label = Label.new("tau", "proj0", proc.node.target)
      label = Label.new("tau", "proj", proc.node.target)
      add_op = Environment::EnvNode.new("proj1", proc.node.target)
      newproc = proc.copy
      newproc.eliminate_head!
      newenv = env.copy
      newenv.add_head!(add_op)
      newcfg = Configuration.new(newproc, newenv)
      ret << TransNode.new(label, newcfg)
      
      # else discard
      # label_discard = Label.new("tau", "proj1", proc.node.target)
      label_discard = Label.new("tau", "proj", proc.node.target)
      add_op_discard = Environment::EnvNode.new("proj0", proc.node.target)

      proc_discard_node = QProcess::ProcessNode.new("discard", nil, proc.qv)
      proc_discard = QProcess.new
      proc_discard.node = proc_discard_node
      env_discard = env.copy
      env_discard.add_head!(add_op_discard)

      cfg_discard = Configuration.new(proc_discard, env_discard)
      ret << TransNode.new(label_discard, cfg_discard)
    when "restriction"
      restr_ch |= proc.node.target
      l_cfg = Configuration.new(proc.left.copy, env.copy)
      tmp_trans = __strong_reduction_inter(l_cfg, restr_ch)
      tmp_trans.each { |trans_i|
        newproc = proc.copy
        newproc.left = trans_i.cfg.proc
        newcfg = Configuration.new(newproc, trans_i.cfg.env)
        ret << TransNode.new(trans_i.label, newcfg)
      }
    else
      raise "Invalid kind #{proc.node.kind}"
    end
        
    ret
  end

  public
  def tau_star(cfg)
    ret = [cfg.copy] # of Configuration
    strongs = __strong_reduction_inter(cfg, [])
    strongs.each { |strong_i|
      if strong_i.label.kind == "tau"
        ret += tau_star(strong_i.cfg)
      end
    }
    
    ret
  end

  def strong_reduction(cfg)
    __strong_reduction_inter(cfg, [])
  end # def strong_reduction(cfg)

end # module Transition
