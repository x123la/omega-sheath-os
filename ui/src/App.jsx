import React, { useState, useEffect, useRef, useMemo } from 'react';
import useWebSocket, { ReadyState } from 'react-use-websocket';
import { 
  Activity, 
  ShieldCheck, 
  AlertTriangle, 
  Database, 
  Cpu, 
  Network,
  Clock,
  ChevronRight,
  Hexagon
} from 'lucide-react';
import * as d3 from 'd3';

const WS_URL = 'ws://localhost:4000/ws';

const App = () => {
  const [events, setEvents] = useState([]);
  const [certs, setCerts] = useState([]);
  const [metrics, setMetrics] = useState({
    ingressCount: 0,
    sequencerAccepted: 0,
    sequencerPending: 0,
    certsFinalized: 0,
    lastCertType: 'None'
  });
  const [nodes, setNodes] = useState([]); // For D3
  const [links, setLinks] = useState([]); // For D3

  const { lastJsonMessage, readyState } = useWebSocket(WS_URL, {
    shouldReconnect: (closeEvent) => true,
  });

  useEffect(() => {
    if (lastJsonMessage) {
      handleIncomingMessage(lastJsonMessage);
    }
  }, [lastJsonMessage]);

  const handleIncomingMessage = (msg) => {
    switch (msg.type) {
      case 'ingress':
        setMetrics(prev => ({ ...prev, ingressCount: prev.ingressCount + 1 }));
        const newEvent = msg.event;
        setEvents(prev => [newEvent, ...prev].slice(0, 50));
        
        // Update D3 nodes/links
        setNodes(prev => {
          if (prev.find(n => n.id === newEvent.event_id)) return prev;
          return [...prev, { id: newEvent.event_id, label: `E:${newEvent.event_id}`, type: 'event' }];
        });
        
        if (newEvent.deps && newEvent.deps.length > 0) {
          setLinks(prev => {
            const newLinks = newEvent.deps.map(depId => ({
              source: newEvent.event_id,
              target: depId
            }));
            return [...prev, ...newLinks];
          });
        }
        break;

      case 'sequencer_accepted':
        setMetrics(prev => ({ ...prev, sequencerAccepted: prev.sequencerAccepted + 1 }));
        break;

      case 'sequencer_pending':
        setMetrics(prev => ({ ...prev, sequencerPending: prev.sequencerPending + 1 }));
        break;

      case 'certificate_finalized':
        setMetrics(prev => ({ 
          ...prev, 
          certsFinalized: prev.certsFinalized + 1,
          lastCertType: msg.cert_type
        }));
        setCerts(prev => [msg, ...prev].slice(0, 20));
        break;

      default:
        console.log('Unknown message type:', msg.type);
    }
  };

  const connectionStatus = {
    [ReadyState.CONNECTING]: 'Connecting',
    [ReadyState.OPEN]: 'Live',
    [ReadyState.CLOSING]: 'Closing',
    [ReadyState.CLOSED]: 'Disconnected',
    [ReadyState.UNINSTANTIATED]: 'Uninstantiated',
  }[readyState];

  return (
    <div className="flex h-screen w-screen overflow-hidden bg-slate-950 font-mono text-xs">
      {/* Sidebar */}
      <div className="w-64 border-r border-slate-800 flex flex-col p-4 space-y-6">
        <div className="flex items-center space-x-2 text-brand">
          <Hexagon className="w-8 h-8 fill-brand/20 animate-pulse" />
          <h1 className="text-lg font-black tracking-tighter">OMEGA COMMAND</h1>
        </div>

        <div className="space-y-4">
          <StatusItem 
            icon={<Network className="w-4 h-4" />} 
            label="KERNEL STATUS" 
            value={connectionStatus} 
            color={readyState === ReadyState.OPEN ? 'text-emerald-400' : 'text-alert'}
          />
          <StatusItem icon={<Database className="w-4 h-4" />} label="INGRESS" value={metrics.ingressCount} />
          <StatusItem icon={<ShieldCheck className="w-4 h-4" />} label="CERTIFIED" value={metrics.certsFinalized} />
          <StatusItem icon={<AlertTriangle className="w-4 h-4" />} label="LAST CERT" value={metrics.lastCertType} />
        </div>

        <div className="flex-1 flex flex-col justify-end space-y-2 opacity-50">
          <div className="text-[10px] uppercase tracking-widest border-b border-slate-800 pb-1">System Load</div>
          <div className="h-1 bg-slate-800 rounded-full overflow-hidden">
            <div className="h-full bg-brand w-1/3 animate-[shimmer_2s_infinite]"></div>
          </div>
        </div>
      </div>

      {/* Main Grid */}
      <div className="flex-1 grid grid-cols-12 grid-rows-6 gap-px bg-slate-800">
        
        {/* Sheaf Map (D3) */}
        <div className="col-span-8 row-span-4 bg-slate-950 relative overflow-hidden">
          <div className="absolute top-4 left-4 z-10 bg-slate-900/80 border border-slate-700 px-2 py-1 rounded">
            CAUSAL SHEAF MAP (DAG)
          </div>
          <SheafGraph nodes={nodes} links={links} />
        </div>

        {/* Real-time Event Stream */}
        <div className="col-span-4 row-span-4 bg-slate-950 flex flex-col p-4">
          <div className="mb-2 uppercase tracking-widest text-slate-500 flex justify-between">
            <span>Event Ingress</span>
            <Activity className="w-3 h-3 text-brand" />
          </div>
          <div className="flex-1 overflow-y-auto space-y-1 pr-2 scrollbar-thin scrollbar-thumb-slate-800">
            {events.map((ev, i) => (
              <div key={i} className="group flex items-start space-x-2 border-l-2 border-brand/20 hover:border-brand p-2 bg-slate-900/30 hover:bg-slate-900 transition-colors">
                <div className="text-slate-600">[{ev.lamport}]</div>
                <div className="flex-1">
                  <div className="text-slate-300">ID:{ev.event_id.toString().slice(-8)}</div>
                  <div className="text-[10px] text-slate-500 truncate">
                    Node:{ev.node_id} | Stream:{ev.stream_id}
                  </div>
                </div>
                <ChevronRight className="w-3 h-3 text-slate-700 group-hover:text-brand" />
              </div>
            ))}
          </div>
        </div>

        {/* Consensus Dashboard */}
        <div className="col-span-6 row-span-2 bg-slate-950 p-4 border-t border-slate-800">
          <div className="mb-2 uppercase tracking-widest text-slate-500">BFT Quorum Finalization</div>
          <div className="flex items-center space-x-8 h-full">
            <div className="flex-1 space-y-4">
              <div className="flex justify-between items-end">
                <span className="text-2xl font-bold">{metrics.certsFinalized}</span>
                <span className="text-slate-500">Certificates Finalized</span>
              </div>
              <div className="h-4 bg-slate-900 rounded-sm overflow-hidden border border-slate-800 flex">
                {Array.from({length: 10}).map((_, i) => (
                  <div 
                    key={i} 
                    className={`flex-1 border-r border-slate-950 ${i < (metrics.certsFinalized % 10) ? 'bg-brand' : 'bg-slate-800'}`}
                  />
                ))}
              </div>
            </div>
            <div className="w-32 h-32 border border-brand/20 rounded-full flex items-center justify-center relative">
              <div className="absolute inset-0 border-2 border-dashed border-brand/10 rounded-full animate-[spin_10s_linear_infinite]" />
              <div className="text-center">
                <div className="text-brand font-bold text-lg">99.9%</div>
                <div className="text-[8px] text-slate-500 uppercase">Uptime</div>
              </div>
            </div>
          </div>
        </div>

        {/* Audit Scroll */}
        <div className="col-span-6 row-span-2 bg-slate-950 p-4 border-t border-l border-slate-800">
          <div className="mb-2 uppercase tracking-widest text-slate-500">Certificate Chain</div>
          <div className="overflow-x-auto flex space-x-4 pb-2">
            {certs.map((c, i) => (
              <div key={i} className="min-w-[140px] p-2 bg-slate-900 border border-slate-800 rounded flex flex-col space-y-1">
                <div className={`text-[10px] font-bold ${c.cert_type === 'Merge' ? 'text-emerald-400' : 'text-alert'}`}>
                  {c.cert_type.toUpperCase()}
                </div>
                <div className="text-[9px] text-slate-400 truncate">ID: {c.cert_id}</div>
                <div className="text-[9px] text-slate-500">Nodes: {c.quorum_size} sigs</div>
                <div className="mt-2 text-center py-1 bg-slate-950 rounded text-[8px] text-brand/50 border border-brand/10 uppercase tracking-widest">
                  Verified
                </div>
              </div>
            ))}
          </div>
        </div>

      </div>
    </div>
  );
};

const StatusItem = ({ icon, label, value, color = 'text-slate-300' }) => (
  <div className="flex items-center space-x-3 group">
    <div className="p-2 bg-slate-900 border border-slate-800 rounded group-hover:border-brand/50 transition-colors">
      {icon}
    </div>
    <div className="flex flex-col">
      <span className="text-[9px] text-slate-500 uppercase tracking-tighter">{label}</span>
      <span className={`font-bold ${color}`}>{value}</span>
    </div>
  </div>
);

const SheafGraph = ({ nodes, links }) => {
  const svgRef = useRef();

  useEffect(() => {
    if (!svgRef.current) return;

    const svg = d3.select(svgRef.current);
    const width = svg.node().parentElement.clientWidth;
    const height = svg.node().parentElement.clientHeight;

    svg.selectAll("*").remove();

    const simulation = d3.forceSimulation(nodes)
      .force("link", d3.forceLink(links).id(d => d.id).distance(50))
      .force("charge", d3.forceManyBody().strength(-100))
      .force("center", d3.forceCenter(width / 2, height / 2));

    const link = svg.append("g")
      .attr("stroke", "#1e293b")
      .attr("stroke-opacity", 0.6)
      .selectAll("line")
      .data(links)
      .join("line")
      .attr("stroke-width", 1);

    const node = svg.append("g")
      .attr("stroke", "#00f2ff")
      .attr("stroke-width", 1.5)
      .selectAll("g")
      .data(nodes)
      .join("g");

    node.append("circle")
      .attr("r", 5)
      .attr("fill", d => d.type === 'event' ? "#0f172a" : "#ff003c");

    node.append("text")
      .attr("x", 8)
      .attr("y", "0.31em")
      .text(d => d.label)
      .attr("fill", "#94a3b8")
      .attr("font-size", "8px")
      .attr("pointer-events", "none");

    simulation.on("tick", () => {
      link
        .attr("x1", d => d.source.x)
        .attr("y1", d => d.source.y)
        .attr("x2", d => d.target.x)
        .attr("y2", d => d.target.y);

      node
        .attr("transform", d => `translate(${d.x},${d.y})`);
    });

    return () => simulation.stop();
  }, [nodes, links]);

  return (
    <svg ref={svgRef} width="100%" height="100%" />
  );
};

export default App;