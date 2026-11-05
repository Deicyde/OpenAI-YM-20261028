import YM.PertExtension.TopJet
import YM.Source.ODE

/-! Full linear primary coordinates and inversion of the formal Gaussian Wick
jet within the bare cutoff prescription. No continuum regularization limit. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.PertExtension.Heat.Top
open Function Filter Set Finset RG Wilson Lattice Supply Labels Source Drops InnerProductSpace MeasureTheory Bid MvPolynomial
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
open Push.CutoffProjectors ProjectorNext.Calibration.Coupon Further.CorrectedLift
open Next.Foundations Next.Rank.Normal
variable {G : Gauge}{d : ℕ}{F : Labels.Frame G d}
local notation "V"=> RG.Slot × G.ColorIndex

structure Data (F : Labels.Frame G d) where
  count : F.Index→ℕ
  columns (i) : Fin (count i)→RG.Slot
  shape (i) : Pose G (count i)
  low (i):lows (shape i) (F.grades i).2

def Valid (E : Data F)(S:SectionData F) :=∀ i,S.evaluate (Pi.single i 1) =(lumin (E.shape i) ∘ mapped (E.columns i))
def Harmonious (E : Data F)(H : Hol G) := ∀ i, Projects H (F.basis i) (lumin (E.shape i) ∘ mapped (E.columns i))
lemma chooseData (S : SectionData F)(p : pop S) :∃ E : Data F,Valid E S:=by
  choose m B hB P hp hh using p
  exact ⟨⟨m,B,P,hh⟩,hp⟩
lemma Valid.harmonious {S : SectionData F}(E : Data F)(he : Valid E S){H : Hol G}(h : S.Sound H) : Harmonious E H := by
  intro i;rw [← he i]
  convert! h.projects (Pi.single i 1) using 1
  rw [show (Pi.single i 1 : F.Coeff)=F.coords (F.basis i) from (F.coords_basis _).symm,LinearEquiv.symm_apply_apply]

lemma smooth_symbol (P : MvPolynomial V ℂ) (a : Labels.Jet G) : ContDiff ℝ ω (fun r=>symbolEval (d:=d) P a r):= by
  unfold symbolEval; simp_rw [aeval_eq_eval₂Hom,coe_eval₂Hom,eval₂_eq]
  refine ContDiff.sum fun i hi=>contDiff_const.mul <| contDiff_prod (f:=fun (j:V) (r:ℝ)=>((glow (trunk d (scaleJet a r)) j.1 j.2 :ℂ)^ (i j))) fun j hj=> ?_
  simp_rw [← (Board.pegs (Classical.choice (Hol.exists_ode G)) d).initial]
  exact (Complex.ofRealCLM.contDiff.comp ((EuclideanSpace.proj (𝕜:=ℝ) j.2).contDiff.comp ((Blurb (Classical.choice (Hol.exists_ode G)) d j.1).contDiff.comp (Board.trunk_nice a)))).pow ..

def testLM : MvPolynomial V ℂ →ₗ[ℂ] (Lens G d→ℂ) where
  toFun := Top.test
  map_add' x y := by
    funext a; unfold test; simp only [symbolEval,map_add]
    have hi p : ContDiffAt ℝ (↑a.2.val) (symbolEval (d:=d) p a.1) 0 := (smooth_symbol p a.1 |>.contDiffAt).of_le le_top
    exact iteratedDeriv_fun_add (hi x) (hi y)
  map_smul' c x := by
    funext t; change Top.test ((c • x):MvPolynomial V ℂ) t=c • Top.test x t
    simp_rw [test,symbolEval,map_smul]; exact iteratedDeriv_const_smul_field c _

noncomputable def bank (F : Labels.Frame G d) : F.Coeff →ₗ[ℂ] (Lens G d→ℂ) := LinearMap.pi fun i=>(probe F i).toLinearMap
lemma bank_inj : Injective (bank F) := LinearMap.ker_eq_bot.mp ((Submodule.eq_bot_iff _).mpr (by
  intro i hi; obtain ⟨s,c,hc,h⟩:=probes_bound F
  have hv a : probe F a i=0 := by apply congr_fun (LinearMap.mem_ker.mp hi) a
  specialize h i; simp only [hv,norm_zero,Finset.sum_const_zero] at h
  by_contra hh;exact (not_le_of_gt (mul_pos hc (norm_pos_iff.mpr hh))) h ))
def reconstruct (F : Labels.Frame G d) := LinearMap.leftInverse (bank F)
lemma reconstruct_eq (x : F.Coeff) : reconstruct F (bank F x)=x:= LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr bank_inj) x

attribute [-simp] degree_eq in
def cut {A :Type*}(ℓ:ℕ): Module.End ℂ (MvPolynomial A ℂ):= weightedHomogeneousComponent (fun _:(A)=>1) ℓ
attribute [-simp] degree_eq
@[simp] lemma cut_coeff {α:Type*} (k : ℕ)(p : MvPolynomial α ℂ)(a : α→₀ℕ) : coeff a (cut k p)= if degree a=k then coeff a p else 0:=by unfold cut degree; rw [coeff_weightedHomogeneousComponent]
lemma cut_twice {A : Type*}(i j:ℕ)(p : MvPolynomial A ℂ) : cut i (cut j p)= if i=j then cut j p else 0:=by
  ext a;simp only [cut_coeff];by_cases hj:i=j
  · simp [hj,cut_coeff];aesop
  by_cases ha:degree a=i
  · simp [ha,hj]
  simp [ha,hj] -- fix
lemma cut_cap {A : Type*}{i : ℕ}(p : MvPolynomial A ℂ)(hi : p.totalDegree < i) : cut i p=0 := by
  ext a;by_cases he: a∈p.support
  · have hz : degree a < i:=degree_eq _ |>.trans_lt ((le_totalDegree he).trans_lt hi)
    simp [cut_coeff, hz.ne]
  simp [cut_coeff,(notMem_support_iff).mp he]
lemma cut_bound {A : Type*}(i : ℕ)(p : MvPolynomial A ℂ): (cut i p).totalDegree ≤ i:= by
  apply Finset.sup_le fun x hx=>?_ ;rw [mem_support_iff] at hx; simp only [cut_coeff] at hx;
  change (x.sum fun _ c=>c) ≤ i; rw [←degree_eq]
  by_contra! hh;simp [hh.ne'] at hx
lemma cut_mono {A : Type*}(i : ℕ)(f : A →₀ ℕ)(c : ℂ): cut i (monomial f c)=if degree f=i then monomial f c else 0:= by
 ext x
 by_cases h:x=f
 · subst h;by_cases h:degree x=i <;> simp [h]
 simp [h];by_cases hi:degree f=i <;> simp [hi,Ne.symm h,h]
lemma cut_relabel {A B : Type*}(f : A→B)(i : ℕ)(p:MvPolynomial A ℂ):cut i ((rename f) p)=rename f (cut i p):=by
  induction p using MvPolynomial.induction_on' with
  | monomial x c=>
    have he (u : A →₀ ℕ) : degree (Finsupp.mapDomain f u) = degree u := by
      induction u using Finsupp.induction_linear with
      | zero=>simp [degree,Finsupp.weight_apply]
      | add x y h1 h2 => simp only [Finsupp.mapDomain_add,degree,map_add] at *;rw [h1,h2]
      | single i j=>simp [degree,Finsupp.weight_apply]
    rw [rename_monomial,cut_mono,cut_mono]; by_cases h:degree x=i
    · have ht : degree (Finsupp.mapDomain f x)=i:= (he x).trans h; rw [if_pos ht,if_pos h, rename_monomial]
    · have ht : degree (Finsupp.mapDomain f x)≠i:=(he x).trans_ne h ; rw [if_neg ht, if_neg h,map_zero]
    all_goals simpa only [Finsupp.weight_mapDomain] using h
  | add x y h h'=> simp [map_add,h,h']
lemma cut_factor {A : Type*}(i : ℕ)(r : ℂ)(p : MvPolynomial A ℂ) : cut i (Next.Rank.LiftMark.factors r p)= r^i • cut i p := by
   unfold Next.Rank.LiftMark.factors
   ext x
   simp_rw [cut_coeff, coeff_smul,Next.Rank.Perch.jets_coeff];change (if _ then r^degree x*_ else _)=_
   by_cases h : degree x=i <;> simp [h]
lemma factor_cut {A : Type*} (i : ℕ)(r : ℂ)(p : MvPolynomial A ℂ) : Next.Rank.LiftMark.factors r (cut i p)=r^i •cut i p:=by
   ext x; simp only [Next.Rank.LiftMark.factors,coeff_smul,Next.Rank.Perch.jets_coeff]; change r^degree x*_ = _
   by_cases hi:degree x=i <;> simp [hi]

def joint (F : Labels.Frame G d) : MvPolynomial V ℂ →ₗ[ℂ] F.Coeff := LinearMap.pi (fun i=> LinearMap.proj i ∘ₗ reconstruct F ∘ₗ testLM ∘ₗ cut (F.grades i).2)

variable (D : Data F)(H : Hol G)(hD : Harmonious D H)
def raw (D : Data F)(i:F.Index): MvPolynomial V ℂ:= rawPart (D.columns i) (D.shape i) (F.grades i).2
lemma raw_cap i : (raw D i).totalDegree≤ (F.grades i).2 := (MvPolynomial.totalDegree_rename_le ..).trans (cut_bound ..)
lemma raw_tier i j : cut j (raw D i)=if j=(F.grades i).2 then raw D i else 0:=by
  unfold raw rawPart
  simp_rw [cut_relabel,show cut j (weightedHomogeneousComponent _ (F.grades i).2 _)=_ from cut_twice ..] -- infer
  split_ifs <;> first | exact map_zero _ | rfl

include H hD
lemma test_raw i : testLM (raw D i)= bank F (Pi.single i 1) := funext (fun a=>leading_correct i _ _ (D.low i) (hD i) a)
lemma joint_raw i : joint F (raw D i)=Pi.single i 1 := by
  funext j; change reconstruct F (testLM (cut _ (raw D i))) j = _; rw [raw_tier]
  by_cases h : (F.grades j).2=(F.grades i).2
  · rw [if_pos h,test_raw D H hD,reconstruct_eq]
  rw [if_neg h,map_zero,map_zero,Pi.single_eq_of_ne (by rintro rfl;exact h rfl),Pi.zero_apply]
open Next.Rank

/-- Π obtained from the displayed linear Taylor tests, retaining all off-shell columns. -/
def topFrame : Heat.Frame V F.Index where
  slots i := (F.grades i).2
  basis:= raw D
  joint:=joint F
  retr := joint_raw D H hD
  drops i p hi:=by change reconstruct F (testLM (cut _ p)) i = _; rw [cut_cap p hi,map_zero,map_zero]; rfl
  bound := raw_cap D
  even i:= by
    have h : raw D i=cut (F.grades i).2 (raw D i):=by simp [raw_tier]
    rw [h,factor_cut]
  projects p i := by change reconstruct F (testLM (cut _ (LiftMark.factors _ p))) i = _;rw [cut_factor,map_smul,map_smul,Pi.smul_apply,smul_eq_mul];rfl
end YM.PertExtension.Heat.Top
