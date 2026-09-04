(()=>{'use strict';
const RED=new Set([1,3,5,7,9,12,14,16,18,19,21,23,25,27,30,32,34,36].map(String));
const POCKETS=['0','00',...Array.from({length:36},(_,i)=>String(i+1))],U=POCKETS.filter(x=>x!=='0'&&x!=='00'),MISS13=26/38;
const HIST_HALF_LIFE=60,HIST_DECAY=Math.pow(.5,1/HIST_HALF_LIFE),HIST_EXCLUDE=5;
const NAMES={R:'RED',B:'BLACK',O:'ODD',E:'EVEN',L:'LOW',H:'HIGH',D1:'1st12',D2:'2nd12',D3:'3rd12',C1:'C1',C2:'C2',C3:'C3'},name=n=>NAMES[n]||n;
const cls=v=>v==='0'||v==='00'?'green':RED.has(v)?'red':'black';
const ok=v=>/^(00|0|[1-9]|[12][0-9]|3[0-6])$/.test(String(v));
const F50=[
 {f:'K',a:['R','B'],side:v=>v==='0'||v==='00'?null:RED.has(v)?'R':'B',hit:(n,v)=>n==='R'?RED.has(v):v!=='0'&&v!=='00'&&!RED.has(v)},
 {f:'P',a:['O','E'],side:v=>v==='0'||v==='00'?null:+v%2?'O':'E',hit:(n,v)=>v!=='0'&&v!=='00'&&(n==='O'?+v%2===1:+v%2===0)},
 {f:'R',a:['L','H'],side:v=>+v>=1&&+v<=18?'L':+v>=19&&+v<=36?'H':null,hit:(n,v)=>n==='L'?+v>=1&&+v<=18:+v>=19&&+v<=36}
];
const T13=[
 {f:'D',n:'D1',s:'1st12',hit:v=>+v>=1&&+v<=12},{f:'D',n:'D2',s:'2nd12',hit:v=>+v>=13&&+v<=24},{f:'D',n:'D3',s:'3rd12',hit:v=>+v>=25&&+v<=36},
 {f:'C',n:'C1',s:'C1',hit:v=>v!=='0'&&v!=='00'&&(+v-1)%3===0},{f:'C',n:'C2',s:'C2',hit:v=>v!=='0'&&v!=='00'&&(+v-2)%3===0},{f:'C',n:'C3',s:'C3',hit:v=>v!=='0'&&v!=='00'&&+v%3===0}
];
const ALL_LABELS=[...F50.flatMap(x=>x.a),...T13.map(x=>x.n)],LABEL_FAMILY={R:'K',B:'K',O:'P',E:'P',L:'R',H:'R',D1:'D',D2:'D',D3:'D',C1:'C',C2:'C',C3:'C'},FAMILY_LABELS={K:['R','B'],P:['O','E'],R:['L','H'],D:['D1','D2','D3'],C:['C1','C2','C3']};
const BETS=new Map();for(const d of F50)for(const n of d.a)BETS.set(n,new Set(U.filter(v=>d.hit(n,v))));for(const d of T13)BETS.set(d.n,new Set(U.filter(v=>d.hit(v))));const BET_P=new Map([...BETS].map(([k,s])=>[k,s.size/38]));
const clamp=(x,a,b)=>Math.max(a,Math.min(b,x));
function compat(a,b){const A=BETS.get(a),B=BETS.get(b);if(!A||!B||!A.size)return 0;let x=0;for(const v of A)if(B.has(v))x++;const c=x/A.size,base=B.size/36;return base?c/base-1:0}
function attrBets(p){if(p==='0'||p==='00')return[];const v=+p;return[RED.has(p)?'R':'B',v%2?'O':'E',v<=18?'L':'H']}
function thirdBets(p){if(p==='0'||p==='00')return[];const v=+p;return[v<=12?'D1':v<=24?'D2':'D3',((v-1)%3===0)?'C1':((v-2)%3===0)?'C2':'C3']}
function coldStrength(g){if(g<5)return 0;const rarity=-Math.log10(Math.pow(MISS13,g));return clamp((rarity-.50)/1.50,.20,1)}
class RouletteEngine{
 constructor(history=[]){this.n=0;this.last=null;this.history=[];this.sumW=0;this.sumW2=0;this.histHits=Object.fromEntries(ALL_LABELS.map(x=>[x,0]));this.pocketHits=Object.fromEntries(POCKETS.map(x=>[x,0]));this.states=Object.fromEntries(F50.map(d=>[d.f,{rs:null,rl:0,active:null}]));this.gaps=Object.fromEntries(T13.map(d=>[d.n,0]));for(const v of history.map(String).filter(ok))this.update(v)}
 update(v){v=String(v);if(!ok(v))return false;const d=HIST_DECAY,d2=d*d;this.sumW*=d;this.sumW2*=d2;for(const k of ALL_LABELS)this.histHits[k]*=d;for(const p of POCKETS)this.pocketHits[p]*=d;this.sumW++;this.sumW2++;for(const k of ALL_LABELS)if(BETS.get(k).has(v))this.histHits[k]++;this.pocketHits[v]++;
  for(const def of F50){const st=this.states[def.f],s=def.side(v);if(st.active){st.active.age++;if(s===st.active.t){st.active=null;st.rs=s;st.rl=1}else if(s===st.active.src)st.active.sourceHits++;continue}if(!s){st.rs=null;st.rl=0;continue}if(s===st.rs)st.rl++;else{st.rs=s;st.rl=1}if(st.rl>=5)st.active={src:s,t:def.a[0]===s?def.a[1]:def.a[0],triggerRun:st.rl,sourceHits:st.rl,age:0}}
  for(const def of T13)this.gaps[def.n]=def.hit(v)?0:this.gaps[def.n]+1;this.n++;this.last=v;this.history.push(v);return true}
 _hist(){let sw=0,sw2=0,h=Object.fromEntries(ALL_LABELS.map(x=>[x,0])),p=Object.fromEntries(POCKETS.map(x=>[x,0]));const m=Math.min(HIST_EXCLUDE,this.history.length);for(let age=0;age<m;age++){const w=Math.pow(HIST_DECAY,age),v=this.history[this.history.length-1-age];sw+=w;sw2+=w*w;for(const k of ALL_LABELS)if(BETS.get(k).has(v))h[k]+=w;p[v]+=w}return{sw:this.sumW-sw,sw2:this.sumW2-sw2,h:Object.fromEntries(ALL_LABELS.map(k=>[k,this.histHits[k]-h[k]])),p:Object.fromEntries(POCKETS.map(k=>[k,this.pocketHits[k]-p[k]]))}}
 _pressure(h,p,sw,sw2,minN){if(sw<=0||sw2<=0)return 0;const sd=Math.sqrt(p*(1-p)*sw2);if(!sd)return 0;const z=(p*sw-h)/sd,neff=sw*sw/sw2,conf=Math.min(1,Math.sqrt(neff/minN));return clamp(z*conf,-2,2)}
 historyNetwork(){const a=this._hist(),raw=new Map(ALL_LABELS.map(k=>[k,this._pressure(a.h[k],BET_P.get(k),a.sw,a.sw2,35)])),pocket=new Map(POCKETS.map(p=>[p,this._pressure(a.p[p],1/38,a.sw,a.sw2,50)])),net=new Map();for(const target of ALL_LABELS){const own=raw.get(target)||0,parts=[];for(const fam of ['K','P','R','D','C']){if(fam===LABEL_FAMILY[target])continue;const src=FAMILY_LABELS[fam];parts.push(src.reduce((q,x)=>q+(raw.get(x)||0)*compat(x,target),0)/src.length)}const relational=parts.length?parts.reduce((q,x)=>q+x,0)/parts.length:0;net.set(target,clamp(.72*own+.28*relational,-2,2))}return{raw,net,pocket}}
 model(){const hist=this.historyNetwork(),ss=F50.map(def=>{const st=this.states[def.f];return{...def,rs:st.rs,rl:st.rl,a:st.active?{...st.active}:null}}),as=ss.filter(x=>x.a),cc=T13.map(def=>{const g=this.gaps[def.n],base=coldStrength(g),hn=hist.net.get(def.n)||0,w=base*(1+.15*clamp(hn/2,-1,1));return{...def,g,w,on:g>=5,hist:hn}}),ac=cc.filter(x=>x.on),activeWeights=new Map();for(const s of as){const hn=hist.net.get(s.a.t)||0;activeWeights.set(s.a.t,1+.12*clamp(hn/2,-1,1))}
  const rel13=new Map(T13.map(x=>[x.n,0])),rel50=new Map(F50.flatMap(x=>x.a).map(x=>[x,0]));for(const s of as){const aw=activeWeights.get(s.a.t)||1;for(const t of T13)rel13.set(t.n,(rel13.get(t.n)||0)+aw*compat(s.a.t,t.n))}for(const c of ac)for(const f of F50)for(const n of f.a)rel50.set(n,(rel50.get(n)||0)+c.w*compat(c.n,n));const cMap=new Map(cc.map(x=>[x.n,x]));
  const ranked=POCKETS.map(p=>{if(p==='0'||p==='00')return{p,score:-999,rank:0};const attrs=attrBets(p),thirds=thirdBets(p);let primary=0,cross13=0,coldDirect=0,coldTo50=0;for(const s of as)if(attrs.includes(s.a.t))primary+=activeWeights.get(s.a.t)||1;for(const n of thirds){const r=rel13.get(n)||0;cross13+=.55*r;const c=cMap.get(n);if(c&&c.on)coldDirect+=.65*c.w}for(const n of attrs)coldTo50+=.25*(rel50.get(n)||0);const labels=[...attrs,...thirds],hm=labels.reduce((a,n)=>a+(hist.net.get(n)||0),0)/labels.length,hp=hist.pocket.get(p)||0,history=.14*hm+.04*hp;return{p,score:primary+cross13+coldDirect+coldTo50+history,primary,cross13,coldDirect,coldTo50,history,rank:0}});
  ranked.sort((a,b)=>b.score-a.score||b.primary-a.primary||b.coldDirect-a.coldDirect||b.cross13-a.cross13||b.coldTo50-a.coldTo50||b.history-a.history||(+a.p)-(+b.p));const hasPrediction=as.length>0||ac.length>0;if(hasPrediction){let k=0;for(const x of ranked){if(x.p==='0'||x.p==='00'||x.score<=0)continue;x.rank=++k;if(k===3)break}}return{ss,as,cc,ac,activeWeights,rel13,rel50,hist,ranked,hasPrediction}}
}
function ranked50(m){return m.as.map(x=>{const n=x.a.t,aw=m.activeWeights.get(n)||1,rel=m.rel50.get(n)||0;return{n,score:aw+.25*rel}}).sort((a,b)=>b.score-a.score||name(a.n).localeCompare(name(b.n)))}
function ranked13(m){return m.ac.map(x=>{const rel=m.rel13.get(x.n)||0;return{n:x.n,label:x.s,g:x.g,score:x.w+.35*rel}}).sort((a,b)=>b.score-a.score||b.g-a.g||a.n.localeCompare(b.n))}
window.RT={RouletteEngine,POCKETS,BETS,RED,name,cls,ranked50,ranked13,clamp};
})();