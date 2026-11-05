import YM.MergeProof.ChaletS
import YM.MergeProof.Wicket
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Slide.Clock
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac Menu
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V : Type} [Fintype V][DecidableEq V] {B:Census V} {G:Gauge}{f c:Side}
open GridApprox.Nil Local Extra.Trajectories Source Extra.Multi
variable (A:History G) (r:ℕ→ℕ)(δ u:ℕ→ℝ)(D:∀ N p m:ℕ,m<N→GaugeDoor (A.rep N p (m+1)) (A.rep N p m))
set_option quotPrecheck false
local notation "Kx"=>A.levels
local notation "P"=>A.levels.budget
local notation "Δ"=> (fun k=> (A.levels.budget k).supportExponent-3)
structure Retain (N p k) : Prop where
    days (i:ℕ) : k ≤ i → ∀ hi:i<N,∃ y w, Volant (A.levels.clock.op i p) (D N p i hi) (r i) ((A.levels.budget (i+1)).supportExponent-4) y ((A.levels.budget i).supportExponent+1/2) ((A.levels.budget i).supportExponent+1) 1 w ∧ Duty A r i (δ i) y w
    endow : let Q:= P N; 0 ≤ u N ∧ 0 ≤ Q.supportExponent-3 ∧ let C:ℝ:= A.levels.clock.forcedAllowance N + r N*siteFactor Q.B*u N
                            ((Q.B + Q.B + 1:ℕ):ℝ)^4*C ≤ 3 ∧ Real.exp C-1 ≤ 1
lemma allRetain (h:Moonlit A r δ u D)(p N k:ℕ):Retain A r δ u D N p k:= ⟨fun i _ hi=> h.days N p i hi,h.endow N⟩

variable (p N k:ℕ) (o:∀ m:ℕ,V → Site (A.S.side m p))(w:ℕ → V→ℝ)
local notation "S"=> A.S
local notation "R"=> (A.rep N p)
local notation "C"=> fun i=> Config G (A.S.side i p)
-- single F initial pinned and physical coin. We keep K witnesses existential. tally invoice independent of mode-algebra.
variable (f:∀ m:ℕ,V  → Config G (A.S.side m p)→ℂ)(g:∀ m:ℕ,V→ℕ → Config G (A.S.side m p)→ℂ)(F: V → Config G (A.S.side N p)→ℂ)
local notation "M"=> manifest A p N f g
local notation "T"=> tapes A p N g
variable {k} {q:∀ m:ℕ,m≤N→ Config G (A.S.side m p)→Poly B} (h:A.Selected) (hk:k≤N) (ht:Matchup A r δ p N k o w B) (hh:Retain A r δ u D N p k)
    (hl:∀ i,Nectar A u D p N k o w f g F i)
    (hQ:∀ m:ℕ, k ≤ m  → ∀ hi:m<N,q m hi.le=(A.levels.clock.op m p).push ((A.rep N p (m+1)).beta) (q (m+1) hi))
    (hv:q N le_rfl=birth B (A.rep N p N) F) (he:Integrable (q N le_rfl) (prior G (A.S.side N p)))
local notation "F!"=> Frost A p N o w f g (q:=q)
include h ht hh hl hk hv he
lemma Frost.proofN : F! N le_rfl:=by
       refine ⟨he,fun j=> ?_,?_⟩
       · rw [hv]; exact funext fun U=> (boot ..).trans ((hl j).writes U)
       choose z a hZ H hh' using fun i=> (hl i).patent
       have hx:=hh.endow; have hp: (R N).p=P N:= (h.represents N p N le_rfl).vac
       have hw:= cloth hZ H (fun i=>ht.pos N hk le_rfl i|>.le)
       let L:= P N; let c:= A.levels.clock.forcedAllowance N; let wC:= c+(r N)*siteFactor ((R N).p.B)*u N
       let d0:=Δ N
       have h1 : ((((R N).p.B+(R N).p.B+1:ℕ)):ℝ)^4*wC ≤ (R N).p.supportExponent - d0:=by dsimp only [wC]; rw [hp]; exact hx.2.2.1.trans_eq (by unfold d0; ring)
       have h2 : Real.exp wC-1≤1:=by unfold wC; rw [hp]; exact hx.2.2.2
       have hi:= unveiled B (w N) (ht.pos N hk le_rfl) (R N) F ((h.represents N p N le_rfl).good.labels) z hw (ht.occ _ hk le_rfl) (c:= A.levels.clock.forcedAllowance N) (K:=g N) (L:=f N) hx.1 le_rfl hx.2.1 h1 h2 (fun U=>Tour.bright A h N p N le_rfl U|>.ne') zero_le_one (fun i=> (hl i).stocked _ hk le_rfl) (show ∀ i, _ from hh') (fun i => (hl i).writes)
       have hP: topPitch A N N=d0:= if_pos rfl
       exact ((congr_arg₂ (fun Y e=> Served (R N) (f N) (T N) Y (o N) (w N) e 1) hv hP).mpr hi)

omit hk hv he
include hQ
set_option maxHeartbeats 800000 in
lemma Frost.higher (m) (hm:m<N) (hK:k ≤ m)(IH:F! (m+1) hm): F! m hm.le:=by
       have hm': k ≤ m+1:= hK.trans m.le_succ
       obtain ⟨hR,hY,hc⟩:=IH
       have hH:= hQ m hK hm; unfold Frost; rw [hH]; let P':=(A.levels.clock.op m p).push ((R (m+1)).beta) (q (m+1) hm)
       have hy(j):(fun U=>(P' U).part (B.fire j))= M m j:= (push_get (A.levels.transition_mass ..) hR _).trans (by rw [hY,(hl j).feeds m hK hm])
       refine ⟨StepData.push_integrable (A.levels.transition_mass ..) _ hR,hy,?_⟩
       choose ψ ν y x hf hs hX hD using fun i=> (hl i).sways m hK hm
       obtain ⟨v,g',hj,hb⟩:= hh.days m hK hm
       have hk:= ht.pins m hK hm; rw [← hk] at hD
       let Z:= A.levels.clock.op m p; let x':=Z.ratio.parent ∘ o (m+1); have hP:x'=o m:=hk
       have hC:Occupancy x' (r m):=by rw [hP]; exact ht.occ _ hK hm.le
       have hA:Repegs x' (P m).B (fun i=>δ m*w (m+1) i) (w m) (1/2) 1 B:=by rw [hP]; exact ht.runs _ hK hm
       have he:(P (m+1)).supportExponent-4 ≤ topPitch A N (m+1) := by unfold topPitch; split <;> linarith only
       have hu(U i): (P' U).part (B.fire i)=coin (R m) (f m i) (g m i) U:= congr_fun (hy i) U
       have hΨ(i:V): ∃ Z': Set PhysicalNext.Repeat.Lotus.Wing, Z'.Finite∧Tale Z' (o (m+1) i) (x' i) 1 (f (m+1) i) (T (m+1) i) (T m i) (ν i) (y i) (x i) (D N p m hm):= ⟨ψ i,hf i,hD i⟩
       have hT := Duty.pre A N m p r h hm hb hj (ht.pos _ hm' hm) (ht.pos _ hK hm.le) (F':=f m) (δ:=ν) (s:=y) (r:=x) hc he (ht.next _ hK hm) hC hA (fun i=> (hl i).stocked _ hK hm.le) hu hs hX hΨ
       have hE:topPitch A N m=(P m).supportExponent:= if_neg hm.ne
       exact (congr_arg₂ (fun a e=> Served (R m) (f m) (T m) P' a (w m) e 1) hP.symm hE).mpr hT

include hk hv he
lemma Frost.upper : ∀ m:ℕ, k ≤ m →∀ hm:m≤N,Integrable (q m hm) (prior G (A.S.side m p)) ∧ (∀ j,(fun U=> (q m hm U).part (B.fire j))= manifest A p N f g m j) ∧
    Served (R m) (f m) (T m) (q m hm) (o m) (w m) (topPitch A N m) 1 := by
    intro m hK he'
    induction he' using Nat.decreasingInduction with
    | self=> exact Frost.proofN _ _ _ _ _ _ _ _ _ _ _ _ h hk ht hh hl hv he
    | of_succ m hm IH=>exact Frost.higher A r δ u D p N o w f g F h ht hh hl hQ m hm hK (IH (hK.trans m.le_succ))
end YM.MergeProof.Accent

#print axioms YM.MergeProof.Accent.Frost.upper
