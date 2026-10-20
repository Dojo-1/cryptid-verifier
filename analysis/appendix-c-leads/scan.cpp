// Bounded raw simulator with deterministic per-section reservoir sampling.
// A captured configuration is exact; sampling is not a halting decider.
#include <algorithm>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <random>
#include <stdexcept>
#include <string>
#include <vector>

struct Op { int write=0, move=0, next=-1; };
struct Snap { long long t; int q, pos, lo, hi, key; std::string left, right; };
struct Pool { uint64_t seen=0; std::vector<Snap> sample; };

int main(int argc,char**argv) {
  try {
    if(argc!=7) throw std::runtime_error("scan INPUT OUTPUT STEPS SEED PER_SECTION MAX_SUPPORT");
    std::ifstream in(argv[1]); std::ofstream out(argv[2]);
    if(!in || !out) throw std::runtime_error("cannot open input/output");
    const long long budget=std::stoll(argv[3]);
    const unsigned seed=std::stoul(argv[4]);
    const int cap=std::stoi(argv[5]), max_support=std::stoi(argv[6]);
    if(budget<0 || budget>100000000 || cap<0 || max_support<0) throw std::runtime_error("invalid budget");
    std::string id,tm; int machine_index=0;
    while(in>>id>>tm) {
      std::vector<std::string> rows; size_t at=0;
      for(;;) { auto end=tm.find('_',at); rows.push_back(tm.substr(at,end-at)); if(end==std::string::npos)break; at=end+1; }
      int states=rows.size(), symbols=rows.at(0).size()/3;
      if(!states || symbols<1 || symbols>10) throw std::runtime_error("invalid table");
      std::vector<std::vector<Op>> ops(states,std::vector<Op>(symbols));
      for(int q=0;q<states;q++) {
        if((int)rows[q].size()!=3*symbols) throw std::runtime_error("nonrectangular table");
        for(int a=0;a<symbols;a++) {
          auto s=rows[q].substr(3*a,3);
          if(s=="---") continue;
          if(s[0]<'0' || s[0]>='0'+symbols || (s[1]!='L'&&s[1]!='R') || s[2]<'A'||s[2]>='A'+states)
            throw std::runtime_error("invalid transition");
          ops[q][a]={s[0]-'0',s[1]=='R'?1:-1,s[2]-'A'};
        }
      }
      std::vector<unsigned char> tape(2*budget+5,0); const int offset=budget+2;
      int head=0,q=0,prev=0,lo=0,hi=-1; long long t=0,skipped=0;
      std::mt19937 rng(seed+machine_index++); std::map<int,Pool> pools;
      auto cell=[&](int p)->unsigned char& {return tape.at(offset+p);};
      auto capture=[&](int key) {
        int from=hi<lo?head:std::min(lo,head), to=hi<lo?head-1:std::max(hi,head-1);
        if(to-from+1>max_support) {skipped++;return;}
        auto& pool=pools[key]; pool.seen++;
        uint64_t slot=pool.sample.size();
        if((int)pool.sample.size()>=cap) slot=std::uniform_int_distribution<uint64_t>(0,pool.seen-1)(rng);
        if(slot>=(uint64_t)cap)return;
        Snap s{t,q,head,lo,hi,key,"",""};
        if(hi>=lo) {
          for(int p=lo;p<head;p++) s.left.push_back('0'+cell(p));
          for(int p=head;p<=hi;p++) s.right.push_back('0'+cell(p));
        }
        if((int)pool.sample.size()<cap) pool.sample.push_back(std::move(s));
        else pool.sample[slot]=std::move(s);
      };
      for(;t<budget;t++) {
        auto op=ops[q][cell(head)];
        int location=hi<lo?1:(head<lo?0:(head>hi?2:1));
        bool reverse=prev && op.next>=0 && op.move!=prev;
        bool frontier=hi<lo || head==lo-1 || head==hi+1;
        if(t==0 || reverse || frontier) capture((((q*2+(prev>0))*2+reverse)*3+location));
        if(op.next<0)break;
        cell(head)=op.write;
        if(op.write) {if(hi<lo)lo=hi=head;else {lo=std::min(lo,head);hi=std::max(hi,head);}}
        else if(hi>=lo) {while(lo<=hi && !cell(lo))lo++;while(hi>=lo && !cell(hi))hi--;}
        head+=op.move; prev=op.move; q=op.next;
      }
      std::vector<Snap> snapshots;uint64_t eligible=0;
      for(auto& [key,pool]:pools) {eligible+=pool.seen;for(auto& s:pool.sample)snapshots.push_back(s);}
      std::sort(snapshots.begin(),snapshots.end(),[](auto&a,auto&b){return a.t<b.t;});
      out<<"{\"id\":\""<<id<<"\",\"machine\":\""<<tm<<"\",\"steps\":"<<t
         <<",\"halted\":"<<(ops[q][cell(head)].next<0?"true":"false")
         <<",\"final_state\":"<<q<<",\"final_head\":"<<head<<",\"eligible_events\":"<<eligible
         <<",\"skipped_wide_events\":"<<skipped<<",\"snapshots\":[";
      bool first=true;
      for(auto&s:snapshots) {
        if(!first) out<<',';
        first=false;
        out<<"{\"t\":"<<s.t<<",\"q\":"<<s.q<<",\"head\":"<<s.pos<<",\"lo\":"<<s.lo<<",\"hi\":"<<s.hi
           <<",\"section\":"<<s.key<<",\"left\":\""<<s.left<<"\",\"right\":\""<<s.right<<"\"}";
      }
      out<<"]}\n";out.flush();
      std::cerr<<id<<" steps="<<t<<" samples="<<snapshots.size()<<" eligible="<<eligible<<" skipped="<<skipped<<'\n';
    }
  } catch(const std::exception&e) {std::cerr<<e.what()<<'\n';return 1;}
}
