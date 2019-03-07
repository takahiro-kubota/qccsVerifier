require "configuration"

class ConfigParser
  def initialize
    @config_pairs = Hash.new
  end
  attr_accessor :config_pairs
  
  public
  def parse(cfgs, procs, envs)
    cfgs.each{ |name, body|
      tmp_cfg = Configuration.new
      unless procs[body[0]]
        raise "undeclared process #{body[0]}"
      end
      unless envs[body[1]]
        raise "undeclared environment #{body[1]}"
      end
      tmp_cfg.proc = procs[body[0]].copy
      tmp_cfg.env = envs[body[1]].copy
      @config_pairs[name] = tmp_cfg
    }
  end 
  
  def show_all
    @config_pairs.each{ |name, body|
      p name
      p body
    }
  end
end
  
