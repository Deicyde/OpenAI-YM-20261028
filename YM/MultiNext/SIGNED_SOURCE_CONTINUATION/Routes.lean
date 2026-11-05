import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Averaging
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Channel

set_option warningAsError false

/-!
# PMOM surjectivity of the linearized tested variations

Jointly homogeneous and lower positions, to avoid differentiating
variable gauges. Includes constant-link fields absorbed into affine
site Color; d=0 handled later with empty input. Cost uniform as a
qualitative span (NOT estimates uniform in p). Lean test really reads
edge on sets, so screen variations off X to zero. -/
set_option autoImplicit false
noncomputable section
namespace YM.MultiNext.SignedSource.Mom
open Function Filter Finset Tensor Work Set MeasureTheory RG Wilson Lattice Labels Source Drops Analysis
open Powers Mediator Next.Foundations Pattern Broadcast Averaging
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {d m : ℕ} {n : Side} (o : Site n) (X : Support n)
section
variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma home_add {p q : V→E} {t : ℕ} (h : Powers.home p t) (ht : Powers.home q t) : Powers.home (p+q) t :=
    ⟨h.1.add ht.1, fun i v => by change p _ + q _=i^t • (p _+q _); rw [h.2,ht.2,smul_add]⟩
lemma home_smul {p : V→E} {t : ℕ} (h : Powers.home p t) (r : ℝ) : Powers.home (r • p) t :=
    ⟨contDiff_const.smul h.1,fun i v => by change r • p _=_ • (r • p _); rw [h.2,smul_comm]⟩
lemma home_zero (t : ℕ) : Powers.home (0 : V→E) t := ⟨contDiff_const,fun _ _ => by simp⟩

lemma roof {p : V → E} (h : p∈space V E (m+1)) :
    ∃ f g, Powers.home f (m+1) ∧ g∈space V E m ∧ p=f+g := by
  refine Powers.next (p:=fun p => ∃ f g, Powers.home f (m+1) ∧ g∈Powers.space V E m ∧ p=f+g) ?_ ⟨0,0,home_zero _,(Powers.space V E m).zero_mem,(add_zero _).symm⟩ ?_ ?_ h
  · rintro q ⟨j,hj,H⟩
    rcases eq_or_lt_of_le hj with rfl|he
    · exact ⟨q,0,H,(space V E m).zero_mem,(add_zero _).symm⟩
    exact ⟨0,q,home_zero _,residence H (Nat.le_of_lt_succ he), (zero_add _).symm⟩
  · rintro _ _ ⟨v,f,hv,hf,rfl⟩ ⟨w,p,hw,hp,rfl⟩; exact ⟨v+w,f+p, home_add hv hw,(space V E m).add_mem hf hp,by abel⟩
  rintro c _ ⟨v,f,hv,hf,rfl⟩; exact ⟨c • v,c • f,home_smul hv c,(space V E m).smul_mem _ hf, smul_add ..⟩

lemma base {p : V → E} (h : p∈space V E 0) : Powers.home p 0 := Powers.next (p:=fun i => Powers.home i 0) (k:=0) (fun _ ⟨i,hi,h⟩ => by rwa [show i=0 from Nat.eq_zero_of_le_zero hi] at h) (home_zero 0) (fun _ _ => home_add)
    (fun r _ h => home_smul h r) h
end

def brush (f : E4→G.Color) (J : Snap G d) : Slate G n d := (fun x => - f (stamp o x),J)

lemma brushed (m : ℕ) (f : E4 → G.Color) (J : Snap G d) (h : f∈space E4 G.Color m) (hh : ∀ t : Fin (d-1),m < t.val+2 → J t=0) :
    brush o f J ∈ Sites o X m := ⟨⟨-f,(space E4 G.Color m).neg_mem h,fun _ _ => rfl⟩,hh⟩
lemma incurs (j : ℕ) (v : Labels.Taylor G j) (d : ℕ) (h : j < d-1) (x : Cover) (a : Axis) :
    access (Pi.single (⟨j,h⟩ : Fin (d-1)) v : Snap G d) (x,a)=∫ t in (0:ℝ)..1,v.value a (xyz x+t • basis a) := by
  let k := Pi.single (⟨j,h⟩ : Fin (d-1)) v (M:=fun i => Labels.Taylor G i.val)
  have ht t : partConnection d (expand d k) 1 (x,a) t=v.value a (xyz x+t • basis a) := by
    simp only [partConnection,potential,one_smul]
    rw [Finset.sum_eq_single j]
    · simp only [expand,k,dif_pos h,Pi.single_eq_same]; rfl
    · intro i hi he; simp only [expand,k,dif_pos (mem_range.mp hi),Pi.single_eq_of_ne (show (⟨i,_⟩:Fin (d-1))≠⟨j,h⟩ from fun h => he (congr_arg Fin.val h))]; simp [Taylor.value,Tensor.diagonal]; try rfl
    simp [h]
  change (∫ t in (0:ℝ)..1,partConnection d (expand d k) 1 (x,a) t)=_; simp_rw [ht]

variable (hX : Nonwrapping X o) (hn : 2 ≤ n.val)
include hn hX
private lemma price_stamp (x : Edge (Site n)) (h : needed X x) : stamp o (x.1+Lattice.step x.2) = stamp o x.1+basis x.2 := by
  unfold stamp; rw [lift_end hn hX _ h.1,Pattern.xyz_step]

lemma covers (i : ℕ) (hi : 0 < i) (hd : i ≤ d) (x : Directions G n) (hx : x∈ Maps o X i) :
    ∃ u : Slate G n d,u∈Sites o X i ∧ fderiv ℝ (optic X o) 0 u=x := by
  -- homogeneous split, represent the top weight by gradient & radial
  -- (integration leaves error in lower powers); so true correction is
  -- supplied by induction, without identifying higher nonlinear Hol terms
  -- as polynomials in FORMAL gauges
  induction i using Nat.strong_induction_on generalizing x with
  | h i ih =>
    let L : Slate G n d →L[ℝ] Directions G n := fderiv ℝ (optic X o) 0
    obtain ⟨V,hV,ht⟩:=hx
    change ∃ u,u∈ _ ∧ L u=x
    rcases i with _|j
    · omega
    rcases j with _|k
    · obtain ⟨r,hR,H⟩:= sheet0 (Q:=V) fun i => base (hV i)
      refine ⟨brush o r 0, brushed o X _ _ _ (residence hR le_rfl) (by simp),?_⟩
      funext j; unfold L
      rw [transmitted,ht]; split; swap; rfl
      next h =>
        have hs : (∫ t in (0:ℝ)..1, D (basis j.2) r (stamp o j.1+t • basis j.2))=V j.2 (stamp o j.1) := by
          letI := FiniteDimensional.complete ℝ G.Color
          have he := (base (hV j.2)) -- scaling degree=0
          have hh v : V j.2 v=V j.2 (stamp o j.1) := by
            have hs := he.2 0 v; have ht := he.2 0 (stamp o j.1); simp only [zero_smul,pow_zero,one_smul] at hs ht; rw [← hs, ht];
          calc
            _ = ∫ t in (0:ℝ)..1,V j.2 (stamp o j.1) := intervalIntegral.integral_congr (fun t _ => (H ..).symm.trans (hh _))
            _ = _ := by simp
        have he : access (0:Snap G d) (lift (j.1-o),j.2)=0 := by
          unfold access; rw [humming,map_zero]; simp [field,Tensor.diagonal]; try rfl
        rw [← hs, differential (k:=0) hR]
        change access 0 _ + (-(r _) - -(r _))=_
        rw [he,price_stamp o X hX hn j h]; abel
    -- engineering k+2
    choose P F hP hf hF using fun j => roof (m:=k) (hV j)
    obtain ⟨r,T,hR,hA⟩:= Averaging.locale k (Q:=P) hP
    have hk : k<d-1 := by omega
    let τ : Snap G d := Pi.single (⟨k,hk⟩ : Fin (d-1)) T
    let W := brush o r τ
    have hT : W∈Sites o X (k+2) := brushed o X _ _ _ (residence hR le_rfl) (by
      intro t h; unfold τ; exact Pi.single_eq_of_ne (show t≠(⟨k,hk⟩ : Fin (d-1)) by rintro rfl; simp at h) _)
    -- leading identity modulo power k
    let M a v := (∫ t in (0:ℝ)..1,P a (v+t • basis a)) - P a v
    have hM a : M a∈space E4 G.Color k := by simpa using Averaging.buys (hP a) (basis a)
    have ha : x-L W ∈ Maps o X (k+1) := by
      refine Exists.intro (F-M) ⟨fun j => ?_,fun x' => ?_⟩
      · simpa using (show F j-M j∈space E4 G.Color k from (Powers.space E4 G.Color k).sub_mem (hf j) (hM j))
      let a := x'.2; let v := stamp o x'.1
      rw [Pi.sub_apply,ht]; unfold L; rw [transmitted]; split; swap; simp
      next h =>
        change V a v - (access τ (lift (x'.1-o),a) + (-(r v) - -(r (stamp o _))))=(F a-M a) v
        rw [price_stamp o X hX hn _ h, hF a]
        -- integrals of radial + differences r = ∫ P
        have hi : access τ (lift (x'.1-o),a)=∫ t in (0:ℝ)..1, T.value a (v+t • basis a) := incurs ..
        have hp := differential hR (basis a) v
        have he' : access τ (lift (x'.1-o),a)+ (r (v+basis a)-r v)=(∫ t in (0:ℝ)..1,P a (v+t • basis a)) := by
          simp_rw [hA]; rw [hi,← hp, intervalIntegral.integral_add ?_ ?_]
          · exact (((diag_smooth (T.val a) 1).continuous).comp (by fun_prop : Continuous fun i : ℝ => v+i • basis a)).intervalIntegrable _ _
          exact (((graded hR (basis a)).1.continuous).comp (by fun_prop : Continuous fun i : ℝ => v+i • basis a)).intervalIntegrable _ _
        simp only [Pi.add_apply,Pi.sub_apply,M,←he',v,a]
        abel
    obtain ⟨R',hL,H⟩:= ih (k+1) (by omega) (by omega) (by omega) _ ha
    refine ⟨W+R',(Sites o X (k+2)).add_mem hT ?_,?_⟩
    · obtain ⟨⟨p,hs,hh⟩,hb⟩:=hL
      exact ⟨⟨p,widen _ _ (by omega) hs,hh⟩,fun i hi => hb _ (by omega)⟩
    rw [map_add,H]; abel
end YM.MultiNext.SignedSource.Mom
