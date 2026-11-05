import YM.MergeProof.Copse
import YM.UVNext.COUPLING_RESET.Prefix
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac Menu
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V I J Y : Type}[Fintype V][DecidableEq V] {B:Census V} {G:Gauge}{n:Side}
open GridApprox.Nil Local Extra.Trajectories Source Extra.Multi
variable {t c w v u d : ℝ}{A:Rep G n}{o:V→Site n}{r r':V→ℝ}
lemma slighter (hr:∀ i,0<r i)(hz:∀ i, 0 < r' i)(h: ∀ i,r' i ≤ w*r i)(hv:0≤w)(hw:w ≤ 1): Repegs (n:=n) o A.p.B r r' 0 w B:=by
   intro i hi j hJ; unfold Poly.toll; rw [zero_mul,Real.exp_zero,mul_one]; refine (Finset.prod_le_prod (fun i _=> hz i|>.le) (fun i _=> h i)).trans ?_
   rw [Finset.prod_mul_distrib,Finset.prod_const]; exact mul_le_mul_of_nonneg_right (show w^i.val.card ≤ w from by simpa only [pow_one] using pow_le_pow_of_le_one hv hw (Nat.le_trans (by decide : 1 ≤ 2) hi)) (prod_nonneg fun i _=> hr i|>.le)
variable {X:Config G n→Poly B}{F:V→ Config G n→ℂ} {K:V→Box n→ Config G n→ℂ}
lemma Served.prune (h:Served A F K X o r v c)(hr:∀ i,0<r i)(hz:∀ i, 0 < r' i)(hv:Repegs o A.p.B r r' t w B)(hw:0 ≤ w)(he:u+t≤v)(hd:w*c ≤ d): Served A F K X o r' u d:=by
   obtain ⟨H,Z,h,hH,hZ,ht⟩:= h; refine ⟨H,Z,h,?_,?_,ht⟩
   · exact ((Towed.peg (hH.shrink he le_rfl hr) (fun i=>(h.exp i).1.toBorne) (fun i=>(h.exp i).2) hv hr hz hw)).shrink le_rfl hd hz
   exact ((Towed.peg (hZ.shrink he le_rfl hr) (fun i=>(h.flag i).1.toBorne) (fun i=>(h.flag i).2) hv hr hz hw)).shrink le_rfl hd hz
structure Duty (A:RG.History G)(r:ℕ→ℕ)(x:ℕ)(d t y:ℝ):Prop where
    -- y K spend d mint price saturating, t M allowance=V.Leg spend max ; x=m
    hats : 0 < d ∧ d ≤ 1
    exp : 100 ≤ (A.levels.budget x).supportExponent ∧ 100≤ (A.levels.budget (x+1)).supportExponent
    copper : let T:= (r x)*siteFactor (A.levels.budget (x+1)).B*d+4*d; T+Real.exp T*T≤ t
    stakes : (((A.levels.budget x).B + (A.levels.budget x).B +1 :ℕ):ℝ)^4*(y+(r x)*siteFactor (A.levels.budget x).B*d) ≤ 1/2 ∧
       Real.exp (y+(r x)*siteFactor (A.levels.budget x).B*d)-1 ≤ 1
section
variable (A:RG.History G) (N m p:ℕ)
local notation "f"=> A.S.side (m+1) p
local notation "c"=> A.S.side m p
local notation "X0"=> A.rep N p m
local notation "X1"=> A.rep N p (m+1)
local notation "Z"=> A.levels.clock.op m p
local notation "P0"=> (A.levels.budget m)
local notation "P1"=> (A.levels.budget (m+1))
variable {x:ℝ} {I: V→ℝ} {J:V→ℝ}
    {θ:Config G (A.S.side (m+1) p)→Poly B} {o:V→Site (A.S.side (m+1) p)}
    {F: V→ Config G (A.S.side (m+1) p)→ℂ} {L: Menu.Specialty G (A.S.side (m+1) p) V}
    {F': V→ Config G (A.S.side m p)→ℂ} {L': V→ℕ→ Config G (A.S.side m p)→ℂ}
    {D:GaugeDoor (A.rep N p (m+1)) (A.rep N p m)} (C:ℕ→ℕ)
set_option quotPrecheck false
local notation "P"=> ((Z).push (X1).beta θ)
-- on TAP requires φ aligns. Call arbitrary PE known. ν local paid
lemma Duty.pre (h:A.Selected)(hm:m < N)(hu:Duty A C m d t u)(H:Volant Z D (C m) ((P1).supportExponent-4) t ((P0).supportExponent+1/2) ((P0).supportExponent+1) 1 u)
    (hI:∀ i,0< I i)(hJ:∀ i,0<J i)(h':Served X1 F L θ o I w 1)(hX:(P1).supportExponent-4 ≤ w)
    (hO:Occupancy o (C m))(hO':Occupancy ((Z).ratio.parent ∘ o) (C m)) (hv:Repegs ((Z).ratio.parent ∘ o) (P0).B (fun i=>d*I i) J (1/2) 1 B)
    (hB:∀ i,Dominated (L' i)) (he:∀ U i,(P U).part (B.fire i)=coin X0 (F' i) (L' i) U)
    {s r:V→ℝ}{δ:V→ℂ}(hc:∀ i,2*I i*s i≤1)(hy:∀ i,I i*r i≤1)(hK:∀ i,∃ Z':Set PhysicalNext.Repeat.Lotus.Wing,Z'.Finite∧Tale Z' (o i) ((Z).ratio.parent (o i)) 1 (F i) (L i) (profile (X0).activities (L' i)) (δ i) (s i) (r i) D): Served X0 F' (fun i=>profile (X0).activities (L' i)) P ((Z).ratio.parent ∘ o) J (P0).supportExponent 1 :=by
   let X:= fun i=> d*I i; have ht(i):0 < X i:=mul_pos hu.hats.1 (hI i)
   have hK': (P0)=(X0).p:=(h.represents N p m hm.le).vac.symm; have hk:(P1)=(X1).p:=(h.represents N p _ hm).vac.symm
   have hp := h'.prune (d:=d) hI ht (slighter hI ht (w:=d) (by intro i;rfl) hu.hats.1.le hu.hats.2) hu.hats.1.le (show (P1).supportExponent-4+0≤ w from by rwa [add_zero]) (le_of_eq (mul_one d))
   apply Menu.stroke (o:=o) (a:=1) (W:=d) H ht hJ (h.represents N p _ hm).good ?_ ?_ (h.represents N p m hm.le).good.labels hp he hB hK hO hO' hu.hats.1.le ?_ ?_ ?_ hu.hats.1.le ?_ ?_ ?_ ?_ zero_le_one ?_ ?_ (A.levels.transition_mass ..) (fun U=>(Tour.bright A h N p m hm.le U).ne')
   · linarith only [hu.exp.2]
   · rw [← hk]; linarith only
   · intro i; change 2* (d* _) * _ ≤ _; calc _ = d*(2*I i*s i):= by ring
                                              _ ≤ _ := mul_le_of_le_one_right hu.hats.1.le (hc i)
   · rw [← hk]; exact hu.copper
   · intro i; exact (le_of_eq (mul_assoc ..)).trans (mul_le_of_le_one_right hu.hats.1.le (hy i))
   · rw [← hK']; linarith only
   · linarith only [hu.exp.1]
   · rw [← hK']; exact hu.stakes.1.trans_eq (by ring)
   · rw [← hK']; exact hv
   · rw [mul_one]
   rw [← hK',one_mul]; exact hu.stakes.2
end
end YM.MergeProof.Accent
