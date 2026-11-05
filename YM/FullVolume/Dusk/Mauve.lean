import YM.MergeProof.Biscuit
import YM.FullVolume.Fields.Pond
import YM.FullVolume.Dusk.Penny
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Accent Local Next.Rank Edition Spindle Extra.Multi Motion
open PhysicalNext.Repeat.Legato.Bandage Cells Extraction Exponential Bid
open Relay
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}(C:Family G)(N k m p d:ℕ)(v:C.label d)(a:ℝ)(ha:0<a)(B:Stock.Tabs C.path.levels)
set_option quotPrecheck false
local notation "b!"=> Cells.center C.S p
local notation "T"=> C.path
local notation "P"=> C.path.levels.budget
local notation "F"=> C.labels.level d
local notation "R"=>C.path.rep N p
local notation "L"=>C.localSection d
local notation "X"=>C.factory d N p
local notation "ℓ"=> C.ref d
variable (W:Bid.Worth)(u ψ φ δ:ℕ→ℝ)(ζ:ℕ→ℕ→ℝ)(r:ℕ→ℕ)(D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m))
local notation "γ"=> RelayDifference.gamma
local notation "ρ"=> ζ d
local notation "κ!"=>Real.sqrt (C.path.levels.clock.forcedAllowance N)
structure Mauve :Prop where
   costs : ∀ p k N,1 ≤ k → Ponds C W u ψ φ δ ζ r D p k N
   tabs d : 1 ≤ C.ref d
   back i: 1≤r i
   grows d i: C.ref d ≤ i→0 < ζ d i
   jump d i: C.ref d ≤ i→ φ i*((C.S.block i).val:ℝ)^(d+1)*ζ d i≤ζ d (i+1)
   listens d N p i: C.ref d ≤ i→∀ hm:i<N,∃ η:ℝ,Tones (C.localSection d) C.path N p C.params (ψ i) i η (D N p i hm)
-- separate cost differential. `x near x_n` used when needed. Stencilled if after growth.
variable (H:C.Makes)(h:Mauve C W u ψ φ δ ζ r D)(b:Config G (C.side N p)→ℂ)(Z:Coefficient (C.labels.level d) (C.side N p))(Q U t E e B':ℝ)
-- positive optional 0 discrepancy.Input E start weights.
open RelayDifference (escrow flight)
include H h B
lemma puddingR (hl:C.ref d ≤ N)(hc:Cream C N p d u ζ b Z Q t E) : ∃ v:C.label d,
    32*(1+(C.path.levels.params N).columns)^2*(F).coeffSize (Z.x-(X).terminal.symm v) ≤ 2*(1+(C.path.levels.params N).columns)*Q ∧
      ∀ m k:ℕ,C.ref d ≤ k→k<N → ∀ hm:Stock.Tabs.opens C.path.levels 1 m k, ∀ i:Motion, ∀ hn:m≤N,
      (Cells.center C.S p hn 0).rootTest (C.beta N p) (Motion.dance i (b-C.O N p v 0)) ≤ cider C ζ d m k * E*flight C (-γ) (N,p):=by
    let hh0:= h.costs p (C.ref d) N (h.tabs d); obtain ⟨M,hM,hH,hZ,hY⟩:= (hh0.stocks d le_rfl hl).1.lyrics; have hp: ∀ i≥ℓ,∀ hm:i<N, (∃ η:ℝ,Tones (C.localSection d) C.path N p C.params (ψ i) i η (D N p i hm)) ∧ Carol L T N p i (D N p i hm) (M.tone (i+1)) (M.tone i) (ψ i):=fun i hi hf=>⟨h.listens _ _ _ i hi hf,hZ i hi hf⟩
    obtain ⟨V,hV,hr,hs,hc',hb,HQ,hv⟩:= antilles (L) (T) N p C.params W M (D N p) ψ le_rfl hl le_rfl H.wilson hH hp Z hc.form hc.pay hc.charge hh0.cost hh0.back
    let a:= (V ℓ).a; let v:= (X).terminal a; let c:=(C.path.levels.params N).columns
    let z:= Relay.dualize C.path N p M ℓ N V (-a); have he: (X).terminal.symm v=a:= LinearEquiv.symm_apply_apply ..
    have hh : initial L T N p (-(V ℓ).a) 0=- C.O N p v 0:=by
       have ht := ((C.linearO N p d 0).mk' _).map_neg v; change C.O N p (-v) 0=- C.O N p v 0 at ht; rw [← ht]; unfold Family.O TransferData.cylinder; rw [map_neg,he]
    have hi : (z.voice N).x=Z.x-(X).terminal.symm v:=by
       rw [he]; refine ((hc' (-a)).1).trans ?_; rw [← hH.head.heard.currents,hH.head.out];rfl
    refine ⟨v,?_,fun m k hk hN hm i hn=> ?_⟩
    · rw [← hi]; exact ((Work.G09.cone_cost hh0.cost hh0.back HQ N hl le_rfl).1.trans (Work.G09.cost_finest hh0.cost hh0.back HQ))
    have hu : 0 < E:= by have hz:=hc.dom; have ha:=hc.fuel; have hg:1 ≤ c:= (C.path.levels.params N).columns_ge; nlinarith only [hg,hz,ha]
    let w:= (ζ d k/4)/(‖alto T k d‖*escrow C N k E)
    have hx' (i):0 < ‖alto T i d‖:=by rw [alto_norm]; exact inv_pos.mpr (pow_pos (C.S.a_pos _) _)
    have hζ := h.grows d k hk; have hE:= RelayDifference.escrow_pos (C:=C) (N:=N) (r:=k) hu
    have hx : 0<w:= div_pos (by positivity) (mul_pos (hx' k) hE); let x:= fun i=> march (fun _:Unit=>w) φ k i (); let H0:=h.costs p k N ((h.tabs d).trans hk); obtain ⟨Y,hf,hk',hb,hP,hθ⟩:= (H0.stocks d hk hN.le).2
    have hF:Brine C.path k δ φ:=H0.stay
    have hQ : ∀ i:ℕ,k ≤ i→ march (fun _:Unit=>w) φ k i () * ‖alto C.path i d‖ * (E/gainChart C.path N i) ≤ ζ d i/4:= diet T d k φ (fun i=>ζ d i/4) w hx (fun i p=>(hF.water i p).1) (fun i he=> by have hp:=h.jump d i (hk.trans he); apply le_trans (le_of_eq (b:=(φ i * ((C.S.block i).val:ℝ)^(d+1)* ζ d i)/4) ?_) (div_le_div_of_nonneg_right hp (by norm_num)); change φ i * ((C.S.block i).val:ℝ)^(d+1)*(ζ d i/4) = _; ring) N E hu.le (by apply le_of_eq; rw [mul_assoc]; change w*(‖alto C.path k d‖*escrow C N k E)= _; unfold w; rw [div_mul_cancel₀ _ ((mul_pos (hx' k) hE).ne')])
    obtain ⟨S,t',ht,hK,hx₀⟩:= hc.attains
    have ha:t+(F).coeffSize Z.x ≤ E:= (add_comm ..).trans_le (hc.charge.trans ((le_mul_of_one_le_left hc.fuel.le (show 1 ≤ 4*(1+c) by linarith only [show 1 ≤ c from (C.path.levels.params N).columns_ge])).trans hc.dom))
    · have hy:= toast T C.params (L) W (ζ d) u ψ t k N p M x b D V H.wilson (H.sections d) hk hH hN.le hr (fun i hi'=>hs i (hk.trans hi')) hV (fun i h he=>(hv i (hk.trans h) he).trans hc.dom) hc.form hc.pay ha ht hx₀ hY hK hc.booking (fun i hi _=> march_pos _ _ _ _ _ (fun _=>hx) hF i hi _) (fun i he _=> (h.grows _ _ (hk.trans he)).le) (fun i hk _=>hQ i hk) hu hb hP hθ
      rw [hh,← sub_eq_add_neg] at hy; have hv:Continuous (b-C.O N p v 0):=hc.resumes.sub (C.continuousO ..); refine (pudding_fill C N k m p d B H h.back _ _ _ (ζ d) w i hm hk hN hx hy hf H0.night hk'.level hF H0.mom hv).trans_eq ?_
      have he:=hx' k; unfold w cider; rw [div_div_eq_mul_div,RelayDifference.escrow_eq (p:=p)]; ring
end YM.MergeProof
#print axioms YM.MergeProof.puddingR
