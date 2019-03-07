$:.unshift File.dirname(__FILE__)

require 'optparse'

require "lexer"
require "parser"
require "qprocess"
require "processparser"
require "envparser"
require "eqparser"
require "configparser"
require "transtree"
require "bisimulation"

exit(1) if $0 != __FILE__

opt_hash = Hash.new
opts = OptionParser.new
opts.on("-s") { |v| opt_hash[:s] = true }  
opts.on("-t") { |v| opt_hash[:t] = true }
opts.on("-d") { |v| opt_hash[:d] = true }  
opts.on("-p") { |v| opt_hash[:p] = true }
opts.on("-e") { |v| opt_hash[:e] = true }
opts.on("-u") { |v| opt_hash[:u] = true }
opts.on("-v") { |v| opt_hash[:v] = true }
opts.parse!(ARGV)

if ARGV[0] == nil
  puts "Missing filename"
else
  lexer = Lexer.new
  lexer.lex(ARGV[0])
  lexicon = lexer.lexicon
  # lexer.show

  parser = Parser.new
  parser.parse(lexicon)
  # parser.show

  nametable = parser.nametable
  processes = parser.processes
  environments = parser.environments
  equations = parser.equations
  configurations = parser.configurations

  process_parser = ProcessParser.new
  process_parser.parse_all(processes, nametable)
  #process_parser.show_all

  env_parser = EnvParser.new
  env_parser.parse_all(environments, nametable)
  # env_parser.show_all
  
  eq_parser = EqParser.new

  eq_parser.parse(equations, nametable)
  #eq_parser.show_all
  parsed_processes = process_parser.parsed_processes
  parsed_environments = env_parser.normalform_envs
  parsed_equations = eq_parser.equations

  config_parser = ConfigParser.new
  config_parser.parse(configurations,
                      parsed_processes,
                      parsed_environments)
  #config_parser.show_all
  cfgs = config_parser.config_pairs

  if opt_hash[:s]
    cfgs.each { |name, cfg_i|
      p name
      cfg_i.proc.show_tree
      cfg_i.env.show
    }
    exit(0)
  elsif opt_hash[:t] 
    cfgs.each { |name, cfg_i|
      p name
      transtree = TransTreeGenerator.new
      transtree.gen_transtree(cfg_i)
      transtree.show_tree
    }
    exit(0)
  else
    cfgA = Configuration.new
    cfgB = Configuration.new
    index = 0
    cfgs.each { |name, cfg_i|
      if index == 0
        p "cfgA: " + name
        cfgA = cfg_i
      elsif index == 1
        p "cfgB: " + name
        cfgB = cfg_i
      end
      index += 1
    }
    if index <= 1 
      p "Please define at least two configurations."
      exit(0)
    end
    bisim = Bisimulation.new(cfgA, cfgB, parsed_equations, opt_hash)
    bisim.judge
  end # opt_hash[:t] 
end # if ARGV[0] == nil
