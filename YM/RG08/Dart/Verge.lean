import YM.RG08.Dart.Qual
/-! # Packet capsules through order escalation. Potentials at anchored eyes.
 Emits width-bounded curvature all ranks; not assuming Ward at planted packets.
 No charging path differences on Step's translation-averages. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Dart
open Function Lattice Wilson Exterior Laurent Work.F08 RG Next.Free Bloch Stationary Finset Filter
open UVExt.Paths Push.AbsoluteSums Quire Vale Matrix Analysis Planned.PrimaryIntegral295 Work.F03 Shade Tall
open Wax Town Creek Scores
open scoped Topology BigOperators Real ContDiff Classical Matrix Matrix.Norms.Frobenius
variable {I: Type}[Fintype I][DecidableEq I]{T: Finset I}{r k i j s n t D:ℕ}{G:Gauge}{m:Side}{R v w θ C B:ℝ}
abbrev Cornea (T:Finset I)(W:Type)(D:ℕ)(R:ℝ)(k:ℕ):= Places I →Rooted (Poise T D R) W k
abbrev Swan (T:Finset I)(W:Type)(D:ℕ)(R:ℝ):= (k:ℕ) → Cornea T W D R k
variable {U:Swan T (Loc G 1) D R}
def Portals (n:ℕ)(U:Swan T (Loc G 1) D R): Prop:= ∀ (i:Places I)(x:I→Sight D R),∀ m,∃ V: Link G m→ℝ, AnalyticAt ℝ V 0 ∧ force V ∧ Stained G V ∧ ∀ j < n, Tensor.coeff V j 0= stitch (sampleK T x ∘ U j i) m 0 -- annotate
structure Stint (T:Finset I)(K: Cornea T (Loc G 2) D R k)(w C:ℝ):Prop extends Camp T w K C where
    tidal p: Tidy (K p)
    hue : ∀ (i:Places I)(x:I→Sight D R), Dapple (sampleK T x ∘ K i)
-- splice status. fence records agreement on roots (all test). input Strand.
def pastry (n:ℕ)(Q: Cornea T (Loc G 2) D R k)(p:Places I):= butter (Q p) n
lemma safe_b (h:Portals n U)(he:r<n)(hz:∀ i< r,(U i)=0)(x:Places I)(b:I→Sight D R): Toll (sampleK T b ∘ U r x):= by
   refine ⟨fun m=>?_⟩; obtain ⟨V,hV,hp,H,hK⟩:= h x b m; refine ⟨V,hp,hV,H,?_,hK r he⟩
   intro i hi hh
   have ht := hK i (hi.trans he); rw [hz i hi,show sampleK T b ∘ (0:Cornea T (Loc G 1) D R i) x=0 from funext fun _=> map_zero _, st_zero] at ht; unfold Tensor.coeff at ht; exact (smul_eq_zero.mp ht).resolve_left (by positivity)
def mercury (K:k≤k)(P:Cornea T (Loc G 1) D R k) := fun x : Places I=> dart (P x)
lemma pours_a (h:T.Nonempty)(hp:Camp T (2*w) (U k) C)(he:∀ i,Tidy (U k i))(hw:0<w)(ht:Portals n U)(hx:k<n)(hz:∀ j<k,U j=0) :
   let M:=mercury (le_refl k) (U k)
   Stint T M w (gapPrice w ^k*C) ∧ pastry k M = U k:= by
   let K := mercury (le_refl k) (U k); intro M; have hV:Camp T w M (gapPrice w ^k*C):= camp_foot hp dart (fun V i hv=> thorn hv hw) (by linarith) (pow_nonneg (inv_nonneg.mpr hw.le) _)
   have hk i:=camp_for hp (by positivity) h i
   have hQ i x := Ink.some (hk i) (sampleK T (D:=D) (R:=R) x) (fun i=> Real.exp_pos _|>.le)
   have he' p (x): sampleK (D:=D) (R:=R) T x ∘ M p=dart (sampleK T x∘ U k p):= revolve_eval (thorn_p (hk p) hw) _
   refine ⟨⟨hV,fun i=>spine_s (hk i) hw (he i),fun i x=>?_⟩,funext fun i=>tapUni fun x=>?_⟩
   · rw [he' i x]; exact fun k=> vested k (safe_b ht hx hz ..) (hQ i x) hw
   unfold pastry; rw [butter_f _ (camp_for hV hw.le h i) hw, he' i x]; exact token_preserves hw (Tidy.map _ (he i)) (hQ i x) (safe_b ht hx hz ..)
lemma brings_p {P: Cornea T (Loc G 2) D R k}(h: Stint T P w C)(hv:0<w)(hp:T.Nonempty){U:Swan T (Loc G 1) D R}(he:∀ x,∀ j < n,Pens (U j x))(hg:Portals n U): Portals n (fun j=> U j-pastry j P):=by
   intro x b m; obtain ⟨V,hV,hQ,H,hv'⟩:=hg x b m; let p:= sampleK T b; let F:=p ∘ P x
   have ht:=camp_for h.toCamp hv.le hp x; have hx:= ht.some p (fun i=>Real.exp_pos _|>.le); have hz:=gem_f hx hv (0:Site m) (h.hue x b); have hM:= rise_t hx hv (0:Site m)
   let Q:=rise_a (0:Site m) F; refine ⟨V-Q,hV.sub hM.1,hQ.sub hz.1,fun v=>(H v).sub (hz.2 v),fun j hj=> ?_⟩ -- hM F
   rw [← (show stitch (p ∘ U j x) m 0 - stitch (butter F j) m 0=Tensor.coeff (V-Q) j 0 from ?_)]
   · rw [show sampleK T b ∘ ((fun j=> U j-pastry j P) j x)=(p ∘ U j x)-(p∘ pastry j P x) from funext fun i=>_root_.map_sub .., pastry,butter_f _ ht hv, st_sub ((he x j hj).shaped p).of_norm (butter_h hx hv j|>.pens.of_norm)]
   rw [← hv' j hj, rise_t hx hv _|>.2 j]; unfold Q Tensor.coeff; rw [iteratedFDeriv_sub_apply hV.contDiffAt hM.1.contDiffAt, smul_sub]
lemma notyet {P:Cornea T (Loc G 2) D R k}(h: Stint T P w C)(hv:0<w)(hp:T.Nonempty)(hg:j < k) : pastry j P=0:= by -- j binder
   funext i; refine tapUni fun x=> ?_; unfold pastry; let p:=sampleK T x; have ht:=camp_for h.toCamp hv.le hp i
   rw [butter_f _ ht hv, pearls_z (Ink.some ht _ (fun i=>Real.exp_pos _|>.le)) hv hg]; exact funext fun _=> (map_zero p).symm
abbrev Ample (T:Finset I)(G:Gauge)(D:ℕ)(R:ℝ) := Swan T (Loc G 2) D R
structure Armor (U:Swan T (Loc G 1) D R) (s n:ℕ) (Q:Ample T G D R)(w C:ℝ):Prop where
   funds :∀ i∈Ico s (s+n), Stint T (Q i) w C
   halo (i : ℕ)(hi:i < s+n): U i= ∑ j∈ Ico s (s+n), pastry i (Q j)
private lemma all_bake (T:Finset I)(G:Gauge)(k l D:ℕ)(R:ℝ)(h:0<v): ∃ w C:ℝ,0 < w ∧ w≤ v∧0≤ C ∧ ∀ (U:Cornea T (Loc G 2) D R k)(B:ℝ)(hp:Camp T v U B), ∀ i < l,Camp T w (pastry i U) (C*B):= by
   choose w C hw hW hC H using fun i=> butter_cost (E:=Poise T D R) G k i h
   let E:=range (l+1); have he:E.Nonempty:= ⟨0,by simp [E]⟩
   let σ:= min v (E.inf' he w); refine ⟨σ,∑ i∈E,C i, lt_min h (lt_inf'_iff ..|>.mpr (fun i _=> hw _)), min_le_left .., sum_nonneg fun _ _=>hC _, fun U B hp i hi=> ?_⟩
   have hh:i∈E:=by unfold E; simp; omega
   exact camp_mono (camp_foot hp _ (H i) (hW _) (hC i)) ((min_le_right ..).trans (inf'_le _ hh)) (mul_le_mul_of_nonneg_right (single_le_sum (fun i _=> hC i) hh) hp.pos) -- H quantifier
-- finite escalation. Only Camp needed at used ranks
def Fees (k:ℕ)(F:Swan T (Loc G 1) D R)(w C:ℝ):Prop:=∀ j<k, Camp T w (F j) C ∧ ∀ x,Tidy (F j x)
theorem arose (T:Finset I)(D:ℕ)(R:ℝ)(G:Gauge)(k n:ℕ)(hp:0<w)(hv:T.Nonempty) : ∃ v C:ℝ, 0<v∧v≤w∧0≤C∧∀ (U:Swan T (Loc G 1) D R) (B:ℝ),0≤B→ Fees (k+n) U w B→ Portals (k+n) U→(∀ i< k,U i=0) → ∃ Q: Ample T G D R, Armor U k n Q v (B*C):=by
    induction n generalizing k w with
    | zero=>refine ⟨w,0,hp,le_rfl,le_rfl,fun U b hb hh ho hz=> ⟨0, ⟨fun i hi=> ?_,fun i hi=>?_⟩⟩⟩; simp only [add_zero,Ico_self,notMem_empty] at hi; rw [hz i (by omega),add_zero,Ico_self,sum_empty]
    | succ n ih=>
      let y:= w/2; have hy:0<y:=by unfold y; positivity
      let l:=k+n+1
      obtain ⟨v,C,hv',he,hC,H⟩:= all_bake T G k l D R hy
      obtain ⟨x,K,hx,hk,hK,V⟩:= ih (k+1) hv'
      let S:=gapPrice y ^ k; have hh:0 ≤ S:= pow_nonneg (inv_nonneg.mpr hy.le) _
      have hw:v≤w:= he.trans (half_le_self hp.le)
      refine ⟨x,S+(1+C*S)*K,hx,hk.trans hw,by positivity,fun U B hB hf hQ hP=>?_⟩
      let M:=mercury (le_refl k) (U k); let W i:= U i - pastry i M; have hv : k+1+n=k+(n+1):= by omega
      obtain ⟨hZ,HZ⟩:= pours_a (U:=U) (k:=k) ‹T.Nonempty› (camp_mono (hf k (by omega)).1 (show 2*y ≤ w by unfold y; linarith) le_rfl) (hf k (by omega)|>.2) hy hQ (by omega) hP
      have heA:Fees (k+1+n) W v (B*(1+C*S)) := by
         intro i hi
         have hh:= hf i (hv ▸ hi); have hB(x): Tidy (pastry i M x):= butter_h (camp_for hZ.toCamp hy.le ‹_› x) hy _
         exact ⟨camp_mono (camp_less (camp_mono hh.1 hw le_rfl) (H M _ hZ.toCamp i (by unfold l; omega))) le_rfl (le_of_eq (by unfold S; ring)),fun x=> (hh.2 x).less (hB x)⟩
      have hkD : Portals (k+1+n) W:= by rw [hv]; exact brings_p hZ hy ‹_› (fun x j hj=> ((hf _ hj|>.2 x).pens)) hQ
      have Wz:∀ i< k+1,W i=0:= by intro i hi; by_cases hs:i=k; subst i; exact sub_eq_zero.mpr HZ.symm; unfold W; rw [hP _ (by omega), show pastry i M=0 from notyet hZ hy ‹_› (by omega), sub_zero]
      obtain ⟨N,N'⟩:= V W (B*(1+C*S)) (by positivity) heA hkD Wz
      have hu : Ico k (k+(n+1))=insert k (Ico (k+1) (k+1+n)) := Finset.ext fun i=> by simp only [mem_insert,mem_Ico]; omega
      refine ⟨update N k M,fun i hi=>?_,fun i hi=>?_⟩
      · rw [hu,mem_insert] at hi; obtain h|h:=hi; subst i; rw [update_self]; exact {toCamp:=camp_mono hZ.toCamp (hk.trans he) (by rw [mul_comm B]; exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) hB), tidal:=hZ.tidal,hue:=hZ.hue}
        have hi:= mem_Ico.mp h; rw [update_of_ne (by omega)]; let hh':=N'.funds i h; exact {hh' with toCamp:=camp_mono hh'.toCamp le_rfl (by nlinarith [mul_nonneg hB hh])}
      rw [hu,sum_insert (by simp), update_self]; have hE:=N'.halo i (by omega); unfold W at hE; rw [Finset.sum_congr (f:=fun j=>pastry i (Function.update N k M j)) (g:=fun j=>pastry i (N j)) rfl (fun j hj=>by rw [update_of_ne]; have hh:=mem_Ico.mp hj; omega), add_comm (pastry i M), ← (eq_add_of_sub_eq hE)]
end YM.RG08.Dart
