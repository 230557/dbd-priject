const express=require('express'),http=require('http'),{Server}=require('socket.io'),path=require('path');
const app=express(),server=http.createServer(app),io=new Server(server,{cors:{origin:'*'}});
app.use(express.static(path.join(__dirname,'public')));

const T=32,CO=40,RO=30,TK=50,SS=100,KS=118,PR=12,SM=1.45,SMAX=100,SD=23,SR=18,AR=90,AC=2000,GN=3,RR=3.0,KAR=Math.PI*0.35,TSS=0.18,TSK=0.12,AMS=2000,MAXP=5,SCRATCH_LIFE=2200;
const Z=0;

function buildMap(){const m=Array.from({length:RO},()=>Array(CO).fill(0));for(let x=0;x<CO;x++){m[Z][x]=1;m[RO-1][x]=1;}for(let y=0;y<RO;y++){m[y][Z]=1;m[y][CO-1]=1;}for(let y=12;y<=17;y++){m[y][Z]=2;m[y][CO-1]=2;}for(const[rx,ry,rw,rh] of[[6,4,5,3],[29,4,5,3],[6,23,5,3],[29,23,5,3],[17,12,6,6],[14,5,3,4],[23,5,3,4],[14,21,3,4],[23,21,3,4],[10,13,3,4],[27,13,3,4]])for(let y=ry;y<ry+rh;y++)for(let x=rx;x<rx+rw;x++)if(y>=Z&&y<RO&&x>=Z&&x<CO)m[y][x]=1;return m;}
const MAP=buildMap(),GD=[{x:4,y:8},{x:35,y:8},{x:20,y:6},{x:4,y:21},{x:35,y:21}],HD=[{x:8,y:15},{x:31,y:15},{x:20,y:4},{x:20,y:25},{x:20,y:10}],rooms={};

const la=(a,b,t)=>{let d=b-a;while(d>Math.PI)d-=Math.PI*2;while(d<-Math.PI)d+=Math.PI*2;return a+d*t;};
const dst=(a,b)=>Math.hypot(a.px-b.px,a.py-b.py);
const pub=()=>Object.values(rooms).filter(r=>r.isPub).map(r=>({id:r.id,players:Object.keys(r.players).length,phase:r.phase}));

function resetRoom(r){r.generators=GD.map((g,i)=>({id:i,px:g.x*T+T/2,py:g.y*T+T/2,progress:0,done:false}));r.hooks=HD.map((h,i)=>({id:i,px:h.x*T+T/2,py:h.y*T+T/2,hookedId:null}));r.exits=[{id:0,side:'left',px:0,py:15*T,open:false,progress:0},{id:1,side:'right',px:(CO-1)*T,py:15*T,open:false,progress:0}];r.gensCompleted=0;r.escaped=0;r.scratchMarks=[];r.genAlerts=[];if(r.ticker)clearInterval(r.ticker);r.ticker=null;}
function mkRoom(id,isPub){let r={id,isPub,phase:'lobby',players:{},inputs:{},botFill:false,botSeq:1};resetRoom(r);return r;}
const lobbyState=r=>({players:Object.values(r.players).map(p=>({id:p.id,role:p.role,prefRole:p.prefRole,name:p.name,isBot:!!p.isBot})),phase:r.phase,botFill:!!r.botFill});
function walls(px,py,room){const r=PR;for(const[cx,cy]of[[px-r,py-r],[px+r,py-r],[px-r,py+r],[px+r,py+r]]){const tx=Math.floor(cx/T),ty=Math.floor(cy/T);if(ty<Z||ty>=RO||tx<Z||tx>=CO||MAP[ty][tx]===1)return true;if(MAP[ty][tx]===2&&!room.exits.some(e=>e.open&&((e.side==='left'&&tx===Z)||(e.side==='right'&&tx===CO-1))))return true;}return false;}

const SP=[{px:4*T,py:4*T},{px:35*T,py:4*T},{px:4*T,py:26*T},{px:35*T,py:26*T}];let sIdx=0;
function mkP(id,role,name,pref,isBot=false){let px=20*T,py=10*T;if(role==='survivor'){const s=SP[sIdx++%SP.length];px=s.px;py=s.py;}return{id,prefRole:pref,role,name,px,py,facing:Math.PI/2,health:role==='spectator'?'spectator':'healthy',stamina:SMAX,isSprinting:false,attackCooldown:0,carrying:null,hookProgress:0,healProgress:0,rescueProgress:0,beingRescued:false,exhaustAuraEnd:0,interactLock:false,speedBoostEnd:0,isBot,botInteractPulse:false,lastScratchAt:0};}

function fillBots(room){
  const humans=Object.values(room.players).filter(p=>!p.isBot);
  while(humans.length+Object.values(room.players).filter(p=>p.isBot).length<MAXP){
    const id=`bot-${room.botSeq++}`;
    room.players[id]=mkP(id,'survivor',`Bot ${room.botSeq-1}`,'bot',true);
    room.inputs[id]={};
  }
}

function openCell(room,x,y){
  if(x<0||x>=CO||y<0||y>=RO)return false;
  if(MAP[y][x]===0)return true;
  return MAP[y][x]===2&&room.exits.some(e=>e.open&&((e.side==='left'&&x===Z)||(e.side==='right'&&x===CO-1)));
}
function nearestOpenCell(room,x,y){
  x=Math.max(0,Math.min(CO-1,x));y=Math.max(0,Math.min(RO-1,y));
  if(openCell(room,x,y))return{x,y};
  for(let radius=1;radius<8;radius++)for(let dy=-radius;dy<=radius;dy++)for(let dx=-radius;dx<=radius;dx++)if(Math.abs(dx)===radius||Math.abs(dy)===radius){const nx=x+dx,ny=y+dy;if(openCell(room,nx,ny))return{x:nx,y:ny};}
  return null;
}
function findBotPath(room,from,target){
  const start=nearestOpenCell(room,Math.floor(from.px/T),Math.floor(from.py/T)),goal=nearestOpenCell(room,Math.floor(target.px/T),Math.floor(target.py/T));
  if(!start||!goal)return[];
  const seen=Array.from({length:RO},()=>Array(CO).fill(false)),prev=Array.from({length:RO},()=>Array(CO).fill(null)),q=[start];seen[start.y][start.x]=true;
  for(let i=0;i<q.length;i++){const c=q[i];if(c.x===goal.x&&c.y===goal.y)break;for(const[dX,dY]of[[1,0],[-1,0],[0,1],[0,-1]]){const nx=c.x+dX,ny=c.y+dY;if(openCell(room,nx,ny)&&!seen[ny][nx]){seen[ny][nx]=true;prev[ny][nx]=c;q.push({x:nx,y:ny});}}}
  if(!seen[goal.y][goal.x])return[];
  const path=[];let c=goal;while(c){path.push(c);c=prev[c.y][c.x];}return path.reverse();
}
function moveBot(bot,target,room,sprint,inp,now){
  if(!target)return;
  const goalKey=`${Math.floor(target.px/T)},${Math.floor(target.py/T)}`;
  if(bot.botLastX!==undefined&&Math.hypot(bot.px-bot.botLastX,bot.py-bot.botLastY)<0.4&&now-(bot.botLastProgress||now)>700){bot.botPath=[];bot.botPathGoal='';bot.botPathIndex=1;bot.botPathAt=0;bot.botDetour=(bot.botDetour||0)+1;}
  if(Math.hypot(bot.px-(bot.botLastX||bot.px),bot.py-(bot.botLastY||bot.py))>=0.4){bot.botLastProgress=now;}
  bot.botLastX=bot.px;bot.botLastY=bot.py;
  if(!bot.botPath||bot.botPathGoal!==goalKey||now-(bot.botPathAt||0)>250){bot.botPath=findBotPath(room,bot,target);bot.botPathGoal=goalKey;bot.botPathAt=now;bot.botPathIndex=1;}
  while(bot.botPath&&bot.botPathIndex<bot.botPath.length&&Math.hypot(bot.px-(bot.botPath[bot.botPathIndex].x*T+T/2),bot.py-(bot.botPath[bot.botPathIndex].y*T+T/2))<18)bot.botPathIndex++;
  const next=bot.botPath&&bot.botPath[bot.botPathIndex];
  const waypoint=next?{px:next.x*T+T/2,py:next.y*T+T/2}:target;
  const dx=waypoint.px-bot.px,dy=waypoint.py-bot.py,ang=Math.atan2(dy,dx);
  bot._botAngle=ang;
  inp.up=0;inp.down=0;inp.left=0;inp.right=0;
  if(Math.abs(dx)>Math.abs(dy)){if(dx<0)inp.left=1;else if(dx>0)inp.right=1;}else if(dy<0)inp.up=1;else if(dy>0)inp.down=1;
  const probe=inp.left?-1:inp.right?1:0,probeY=inp.up?-1:inp.down?1:0;
  if((probe||probeY)&&walls(bot.px+probe*KS*0.08,bot.py+probeY*KS*0.08,room)){
    inp.up=inp.down=inp.left=inp.right=0;
    const secondary=Math.abs(dx)>Math.abs(dy)?[0,Math.sign(dy)]:[Math.sign(dx),0],primary=[probe,probeY],options=[secondary,primary,[-secondary[0],-secondary[1]],[-primary[0],-primary[1]]];
    for(const[dX,dY]of options)if((dX||dY)&&!walls(bot.px+dX*KS*0.08,bot.py+dY*KS*0.08,room)){if(dX<0)inp.left=1;if(dX>0)inp.right=1;if(dY<0)inp.up=1;if(dY>0)inp.down=1;break;}
  }
  inp.sprint=sprint?1:0;inp.camAngle=0;
}

function botThink(room,bot,now){
  const inp={up:0,down:0,left:0,right:0,sprint:0,attack:0,interact:0,action:null,camAngle:0};
  const surv=Object.values(room.players).filter(p=>p.role==='survivor');
  if(bot.role==='survivor'){
    if(['hooked','downed','carried','escaped','sacrificed'].includes(bot.health)){room.inputs[bot.id]=inp;return;}
    const killer=Object.values(room.players).find(p=>p.role==='killer');
    const threat=killer&&dst(bot,killer)<220;
    const hooked=surv.filter(p=>p.health==='hooked'&&p.id!==bot.id).sort((a,b)=>dst(bot,a)-dst(bot,b))[0];
    const rescueCandidates=hooked&&surv.filter(p=>['healthy','injured'].includes(p.health));
    const safeRescuers=killer&&rescueCandidates?rescueCandidates.filter(p=>dst(p,killer)>260):rescueCandidates;
    const rescuer=hooked&&(safeRescuers?.length?safeRescuers:rescueCandidates)?.sort((a,b)=>dst(a,hooked)-dst(b,hooked))[0];
    const heal=surv.filter(p=>p.id!==bot.id&&['injured','downed'].includes(p.health)).sort((a,b)=>dst(bot,a)-dst(bot,b))[0];
    let target=null,action=null,range=55;
    if(hooked&&rescuer&&rescuer.id===bot.id){target=hooked;action={type:'rescue',id:hooked.id};range=58;}
    else if(heal&&bot.health==='healthy'){target=heal;action={type:'heal',id:heal.id};range=48;}
    else if(room.gensCompleted<GN){target=room.generators.filter(g=>!g.done).sort((a,b)=>dst(bot,a)-dst(bot,b))[0];action=target&&{type:'repair',id:target.id};range=76;}
    else{target=room.exits.filter(e=>!e.open).sort((a,b)=>dst(bot,a)-dst(bot,b))[0];action=target&&{type:'exit',id:target.id};range=76;}
    if(threat&&!(hooked&&rescuer&&rescuer.id===bot.id&&dst(bot,hooked)<110)){const away={px:Math.max(T*1.5,Math.min((CO-1.5)*T,bot.px+(bot.px-killer.px)*4)),py:Math.max(T*1.5,Math.min((RO-1.5)*T,bot.py+(bot.py-killer.py)*4))};moveBot(bot,away,room,true,inp,now);}
    else if(target&&dst(bot,target)>range)moveBot(bot,target,room,true,inp,now);
    else if(action)inp.action=action;
  }else if(bot.role==='killer'){
    const carrying=bot.carrying&&surv.find(s=>s.id===bot.carrying);
    const downed=surv.filter(s=>s.health==='downed').sort((a,b)=>dst(bot,a)-dst(bot,b))[0];
    const hook=room.hooks.filter(h=>!h.hookedId).sort((a,b)=>dst(bot,a)-dst(bot,b))[0];
    const target=carrying?(hook||{px:bot.px,py:bot.py}):downed||surv.filter(s=>!['escaped','sacrificed','hooked'].includes(s.health)).sort((a,b)=>dst(bot,a)-dst(bot,b))[0];
    if(target&&dst(bot,target)>55)moveBot(bot,target,room,false,inp,now);
    const victim=surv.filter(s=>['healthy','injured'].includes(s.health)).sort((a,b)=>dst(bot,a)-dst(bot,b))[0];
    if(victim&&dst(bot,victim)<=AR+5){inp.attack=1;bot.botAttackTarget=victim.id;}
    const canInteract=(!carrying&&downed&&dst(bot,downed)<60)||(!!carrying&&hook&&dst(bot,hook)<70);
    if(canInteract&&!bot.botInteractPulse){inp.interact=1;bot.botInteractPulse=true;}else if(!canInteract)bot.botInteractPulse=false;
  }
  room.inputs[bot.id]=inp;
}

function tick(room){
  try {
    const dt=TK/1000,now=Date.now(),pls=Object.values(room.players),killer=pls.find(p=>p.role==='killer'),surv=pls.filter(p=>p.role==='survivor');

    pls.filter(p=>p.isBot).forEach(p=>botThink(room,p,now));
    surv.forEach(s=>s.beingRescued=false);
    surv.forEach(s=>{
      const a=(room.inputs[s.id]||{}).action;
      if(a&&a.type==='rescue'){
        const hk=surv.find(o=>o.health==='hooked'&&o.id===a.id&&dst(s,o)<60);
        if(hk){
          hk.beingRescued=true;
          if(['healthy','injured'].includes(s.health)){hk.rescueProgress=Math.min(100,(hk.rescueProgress||0)+RR*dt*8);if(hk.rescueProgress>=100){hk.health='injured';hk.hookProgress=0;hk.rescueProgress=0;const h=room.hooks.find(x=>x.hookedId===hk.id);if(h)h.hookedId=null;}}
        }
      }
    });

    for(const s of surv){if(s.health==='hooked'){if(!s.beingRescued){s.hookProgress+=(100/60)*dt;s.rescueProgress=0;}if(s.hookProgress>=100){s.health='sacrificed';const h=room.hooks.find(k=>k.hookedId===s.id);if(h)h.hookedId=null;}}}

    for(const s of surv){
      if(['hooked','downed','escaped','sacrificed','carried','spectator'].includes(s.health)){s.isSprinting=false;continue;}
      const inp=room.inputs[s.id]||{},action=inp.action||null;let dx=0,dy=0;
      if(inp.up)dy-=1;if(inp.down)dy+=1;if(inp.left)dx-=1;if(inp.right)dx+=1;
      const mv=(dx!==0||dy!==0),sp=!!inp.sprint;

      if(mv&&sp){s.stamina=Math.max(0,s.stamina-SD*dt);if(s.stamina===0)s.exhaustAuraEnd=now+AMS;}
      else s.stamina=Math.min(SMAX,s.stamina+SR*dt);

       s.isSprinting=(mv&&sp&&s.stamina>0);

      if(mv){
        let ma=Math.atan2(dy,dx)+(typeof inp.camAngle==='number'?inp.camAngle:s.facing+Math.PI/2);
        s.facing=la(s.facing,ma,TSS);
        let spd=SS;
        if(now < (s.speedBoostEnd||0)){
          spd*=1.7;
        }else{
          spd*=(sp?(s.stamina>0?SM:1.15):1)*(s.health==='injured'?0.75:1);
        }
        const mx=Math.cos(ma)*spd*dt,my=Math.sin(ma)*spd*dt;
        if(!walls(s.px+mx,s.py,room))s.px+=mx;
        if(!walls(s.px,s.py+my,room))s.py+=my;
         if(mv&&sp&&now-(s.lastScratchAt||0)>110){room.scratchMarks.push({px:s.px,py:s.py,facing:s.facing,createdAt:now});s.lastScratchAt=now;}
      }

      if(action&&action.type!=='rescue'&&['healthy','injured'].includes(s.health)){
        if(action.type==='heal'){const tg=surv.find(o=>o.id===action.id&&['injured','downed'].includes(o.health)&&dst(s,o)<50);if(tg){tg.healProgress=Math.min(100,(tg.healProgress||0)+RR*dt*2);if(tg.healProgress>=100){tg.health=tg.health==='downed'?'injured':'healthy';tg.healProgress=0;}}}
        else if(action.type==='repair'){const g=room.generators[action.id];if(g&&!g.done&&dst(s,g)<80){g.progress=Math.min(100,g.progress+RR*dt);if(g.progress>=100){g.done=true;room.gensCompleted++;io.to(room.id).emit('genComplete',{id:g.id,total:room.gensCompleted});}}}
        else if(action.type==='exit'&&room.gensCompleted>=GN){const ex=room.exits[action.id];if(ex&&!ex.open&&dst(s,ex)<80){ex.progress=Math.min(100,ex.progress+RR*dt*0.5);if(ex.progress>=100){ex.open=true;io.to(room.id).emit('exitOpen',{id:ex.id});}}}
      }
    }

    if(killer){const inp=room.inputs[killer.id]||{};let dx=0,dy=0;if(inp.up)dy-=1;if(inp.down)dy+=1;if(inp.left)dx-=1;if(inp.right)dx+=1;if(dx!==0||dy!==0){let ma=Math.atan2(dy,dx)+(typeof inp.camAngle==='number'?inp.camAngle:killer.facing+Math.PI/2);killer.facing=la(killer.facing,ma,TSK);const mx=Math.cos(ma)*KS*dt,my=Math.sin(ma)*KS*dt;if(!walls(killer.px+mx,killer.py,room))killer.px+=mx;if(!walls(killer.px,killer.py+my,room))killer.py+=my;}
      if(killer.carrying){const c=surv.find(s=>s.id===killer.carrying);if(c){c.px=killer.px;c.py=killer.py-15;}}
      if(killer.isBot&&inp.attack&&killer.botAttackTarget){const victim=surv.find(s=>s.id===killer.botAttackTarget&&['healthy','injured'].includes(s.health));if(victim&&dst(killer,victim)<AR)killer.facing=Math.atan2(victim.py-killer.py,victim.px-killer.px);}
      if(inp.attack&&now-killer.attackCooldown>AC&&!killer.carrying){killer.attackCooldown=now;for(const s of surv){if(['healthy','injured'].includes(s.health)&&dst(killer,s)<AR){let d=Math.abs(Math.atan2(s.py-killer.py,s.px-killer.px)-killer.facing);while(d>Math.PI)d-=Math.PI*2;if(Math.abs(d)<=KAR/2){s.health=s.health==='healthy'?'injured':'downed';if(s.health==='injured')s.speedBoostEnd=now+5000;io.to(room.id).emit('hit',{id:s.id,health:s.health});}}}}
      if(inp.interact&&!killer.interactLock){killer.interactLock=true;if(!killer.carrying){const dn=surv.find(s=>s.health==='downed'&&dst(killer,s)<60);if(dn){killer.carrying=dn.id;dn.health='carried';}}else{const hk=room.hooks.find(h=>!h.hookedId&&dst(killer,h)<70);if(hk){const c=surv.find(s=>s.id===killer.carrying);if(c){c.health='hooked';c.px=hk.px;c.py=hk.py;c.hookProgress=0;hk.hookedId=c.id;killer.carrying=null;}}}}
      if(!inp.interact)killer.interactLock=false;}

    for(const s of surv)if(!['escaped','sacrificed','downed','carried','hooked','spectator'].includes(s.health))for(const ex of room.exits)if(ex.open&&dst(s,ex)<30){s.health='escaped';room.escaped++;io.to(room.id).emit('escaped',{id:s.id});}

    const act=surv.filter(s=>!['sacrificed','escaped','spectator'].includes(s.health));
    if(act.length>0&&act.every(s=>['downed','carried','hooked'].includes(s.health))){room.phase='killerWin';clearInterval(room.ticker);io.to(room.id).emit('gameOver',{result:'killerWin'});io.emit('roomList',pub());}
    else if(surv.length>0&&surv.every(s=>['escaped','sacrificed','spectator'].includes(s.health))){room.phase='survivorWin';clearInterval(room.ticker);io.to(room.id).emit('gameOver',{result:'survivorWin'});io.emit('roomList',pub());}

     room.scratchMarks=room.scratchMarks.filter(m=>now-m.createdAt<SCRATCH_LIFE);
     room.genAlerts=room.genAlerts.filter(a=>now<a.until);
     const state={phase:room.phase,gensCompleted:room.gensCompleted,escaped:room.escaped,generators:room.generators,exits:room.exits,hooks:room.hooks,scratchMarks:[],genAlerts:[],players:Object.values(room.players).map(p=>({id:p.id,name:p.name,role:p.role,px:p.px,py:p.py,facing:p.facing,health:p.health,stamina:p.stamina,isSprinting:p.isSprinting,attackCooldown:p.attackCooldown,carrying:p.carrying,hookProgress:p.hookProgress,healProgress:p.healProgress,rescueProgress:p.rescueProgress,exhaustAuraEnd:p.exhaustAuraEnd||0,isBot:!!p.isBot}))};
     Object.values(room.players).filter(p=>!p.isBot).forEach(p=>io.to(p.id).emit('state',p.role==='killer'?{...state,scratchMarks:room.scratchMarks,genAlerts:room.genAlerts}:state));
  } catch(e) {
    console.error("Tick error:", e);
  }
}

io.on('connection',socket=>{
  socket.on('getRooms',()=>socket.emit('roomList',pub()));
   socket.on('joinRoom',({roomId,prefRole,name,isPub})=>{roomId=roomId||'room1';if(!rooms[roomId])rooms[roomId]=mkRoom(roomId,isPub);const room=rooms[roomId];if(Object.values(room.players).filter(p=>!p.isBot).length>=MAXP)return socket.emit('error','Room full!');let role=prefRole;if(room.phase==='playing')role='spectator';socket.join(room.id);socket.roomId=room.id;room.players[socket.id]=mkP(socket.id,role,(name||`P-${socket.id.slice(0,4)}`).substring(0,10),prefRole);room.inputs[socket.id]={};socket.emit('joined',{playerId:socket.id,map:MAP,roomId:room.id,phase:room.phase});io.to(room.id).emit('lobbyUpdate',lobbyState(room));io.emit('roomList',pub());});
  socket.on('chat',msg=>{const room=rooms[socket.roomId];if(room&&room.players[socket.id]&&typeof msg==='string')io.to(room.id).emit('chat',{name:room.players[socket.id].name,msg:msg.substring(0,100)});});
   socket.on('setBotFill',enabled=>{const room=rooms[socket.roomId];if(!room||room.phase!=='lobby'||!room.players[socket.id])return;room.botFill=!!enabled;io.to(room.id).emit('lobbyUpdate',lobbyState(room));});
   socket.on('startGame',()=>{const room=rooms[socket.roomId];if(!room||room.phase!=='lobby')return;const humans=Object.values(room.players).filter(p=>!p.isBot);if(room.botFill)fillBots(room);const pl=Object.values(room.players).filter(p=>p.role!=='spectator');if(pl.length<2)return socket.emit('error',room.botFill?'Unable to fill this lobby.':'Need at least 2 players!');const ks=pl.filter(p=>p.prefRole==='killer'&&!p.isBot);let ch=ks.length?ks[Math.floor(Math.random()*ks.length)]:null;if(!ch&&room.botFill)ch=pl.find(p=>p.isBot)||pl[Math.floor(Math.random()*pl.length)];if(!ch)ch=pl[Math.floor(Math.random()*pl.length)];pl.forEach(p=>{p.role=p.id===ch.id?'killer':'survivor';Object.assign(p,mkP(p.id,p.role,p.name,p.prefRole,p.isBot));});room.phase='playing';sIdx=0;resetRoom(room);room.ticker=setInterval(()=>tick(room),TK);io.to(room.id).emit('gameStart',{});io.emit('roomList',pub());});
   socket.on('backToLobby',()=>{const room=rooms[socket.roomId];if(!room||room.phase==='playing')return;room.phase='lobby';Object.keys(room.players).filter(id=>room.players[id].isBot).forEach(id=>{delete room.players[id];delete room.inputs[id];});resetRoom(room);Object.values(room.players).forEach(p=>{p.role=p.prefRole;p.health='healthy';});io.to(room.id).emit('lobbyUpdate',lobbyState(room));io.emit('roomList',pub());});

  socket.on('skillCheck',({type,id,result})=>{
    const room=rooms[socket.roomId];if(!room||room.phase!=='playing')return;
    if(result==='fail'){
      if(type==='repair'&&room.generators[id]){
        room.generators[id].progress=Math.max(0,room.generators[id].progress-8);
        const alertNow=Date.now();room.genAlerts.push({id,px:room.generators[id].px,py:room.generators[id].py,createdAt:alertNow,until:alertNow+3500});
        io.to(room.id).emit('effect',{px:room.generators[id].px,py:room.generators[id].py,type:'spark'});
        const kp=Object.values(room.players).find(p=>p.role==='killer');
        if(kp){const ks=io.sockets.sockets.get(kp.id);if(ks)ks.emit('genAlert',{px:room.generators[id].px,py:room.generators[id].py});}
      }else if(type==='heal'&&room.players[id]){
        room.players[id].healProgress=Math.max(0,room.players[id].healProgress-8);
        io.to(room.id).emit('effect',{px:room.players[id].px,py:room.players[id].py,type:'blood'});
      }
    }else if(result==='success'){
      if(type==='repair'&&room.generators[id])room.generators[id].progress=Math.min(100,room.generators[id].progress+3);
      else if(type==='heal'&&room.players[id])room.players[id].healProgress=Math.min(100,room.players[id].healProgress+3);
    }
  });

  socket.on('input',inp=>{if(rooms[socket.roomId]&&rooms[socket.roomId].phase==='playing')rooms[socket.roomId].inputs[socket.id]=inp;});
   socket.on('disconnect',()=>{const room=rooms[socket.roomId];if(!room)return;delete room.players[socket.id];delete room.inputs[socket.id];const humans=Object.values(room.players).filter(p=>!p.isBot);if(humans.length===0){if(room.ticker)clearInterval(room.ticker);delete rooms[socket.roomId];}else io.to(room.id).emit('lobbyUpdate',lobbyState(room));io.emit('roomList',pub());});
});

server.listen(process.env.PORT||3000,'0.0.0.0',()=>console.log('Server ready'));

