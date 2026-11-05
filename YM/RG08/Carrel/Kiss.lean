import YM.RG08.Carrel.Chord
import YM.Planned.PRIMARY_INTEGRAL_295.Drupes

/-!
# Actual analytic slots on an arbitrary finite period without cutoff (and their deck cost).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Carrel
open scoped ContDiff Topology BigOperators PowerSeries Classical Matrix.Norms.Frobenius RealInnerProductSpace
open Camera Cloud Room Glyph
open Lattice Laurent Forms Pert.Bulk Isles Packets Filter Finset Function RG
open Wilson Exterior Push.Uniform Precision Work.F03
variable {G:Gauge}{n:ℕ}{P:Side}

abbrev Bedge (G:Gauge)(P:Side):=Cove P (Rayk G 1)
def heavy (G:Gauge): (G.ColorIndex→ℝ) ≃L[ℝ] G.Color := (PiLp.continuousLinearEquiv 2 ℝ (fun _:G.ColorIndex=>ℝ)).symm
def offer (G:Gauge)(e:Edge (Site P)):Cellar (Bedge G P)→L[ℝ] G.Color:=
 (heavy G).toContinuousLinearMap.comp (ContinuousLinearMap.pi (fun i=> ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:Bedge G P=>ℝ) (e.1,coord e.2,i)))
lemma inserts (G:Gauge)(e:Edge (Site P))(x:Cellar (Bedge G P))(u:G.ColorIndex):offer G e x u=x (e.1,coord e.2,u):=rfl

def offers (G:Gauge)(x:Cellar (Bedge G P)):Config G P := fun e=>G.lieExp (offer G e x)
@[simp] lemma offers_z (G:Gauge):offers G (0:Cellar (Bedge G P))=1:=by ext1; simp [offers]
lemma offered (G:Gauge)(e:Edge (Site P)): ‖offer G e‖≤‖(heavy G).toContinuousLinearMap‖:=by
 unfold offer;apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _); intro x
 apply ((heavy G).toContinuousLinearMap.le_opNorm _).trans
 apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
 apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
 intro i; exact norm_le_pi_norm x _

lemma work (G:Gauge)(N:ℕ) : ∃ C:ℝ,1≤C∧∀ (P:Side)(i:Edge (Site P)), Allows N (fun y=>G.mat (offers G y i)) 0 C :=by
 obtain ⟨A,hA,h⟩:=exists_allows (s:={(0:G.Color)}) (f:=fun x=>G.mat (G.lieExp x)) (isCompact_singleton) (fun _ _=> G.exp_jet.contDiffAt) N
 let K:=‖(heavy G).toContinuousLinearMap‖
 let M:=composeCost N A K
 have hM:0≤M:=by unfold M K composeCost;positivity
 refine ⟨1+M,by linarith, fun P i=>?_⟩
 have he:Allows N (fun x:G.Color=>G.mat (G.lieExp x)) (offer G i 0) A:=by rw [map_zero];exact h _ (Set.mem_singleton _)
 have hp:Allows N (offer G i) 0 K:=allows_linear (offered ..) (by simp [K])
 exact (he.comp hp).mono (le_add_of_nonneg_left zero_le_one)

def Kiss (G:Gauge)(p:Site P)(s:Slot) (i:G.ColorIndex) : Still (Bedge G P) := fun x=> s.atSite (offers G x) p i
@[simp] lemma kiss0 (p:Site P)(s:Slot)(i:G.ColorIndex): Kiss G p s i 0=0:=by
 unfold Kiss;rw [atSite_path,offers_z]; simp only [Lattice.faceValue]; have hh(x:Site P)(w:Walk) : travel (1:Config G P) x w=1:=by induction w generalizing x with
 | nil=>rfl
 | cons a w ih=> simp [travel,ih,Step.read]
 simp only [hh,G.curvature_unit,map_zero];rfl

lemma kissing (G:Gauge)(N:ℕ){η:ℝ}(hp:0<η):∃ C:ℝ,1≤C∧∀ (P:Side)(u:Site P)(s:Slot)(i:G.ColorIndex), Allows N (Kiss G u s i) 0 (C*Real.exp (η*s.length)):=by
 obtain ⟨D,hD,h⟩:=work G N
 obtain ⟨M,hM,m⟩:=Planned.PrimaryIntegral295.Drupes.measured _ (show 0≤D by linarith) G N η hp
 -- coord op norm may cost factor norm of heavy^-1
 let B:=‖((heavy G).symm : G.Color →L[ℝ] G.ColorIndex→ℝ)‖
 refine ⟨1+B*M,by have he:0≤B:= norm_nonneg _; nlinarith, fun P u s i=>?_⟩
 let L := (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:G.ColorIndex=>ℝ) i).comp (heavy G).symm.toContinuousLinearMap
 have hL:‖L‖≤B:=by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _);intro x
    exact (norm_le_pi_norm ((heavy G).symm x) i).trans ((heavy G).symm.toContinuousLinearMap.le_opNorm _)
 have hv:= m (V:=offers G (P:=P)) (U:=offers G (P:=P)) (h P) (h P) u s
 apply (hv.linear L hL).mono (le_trans _ (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (Real.exp_pos _).le)) -- may DefEq kink
 rw [mul_assoc]

-- true phase exert: entry derivative at ANY deck occurrence in unpermuted recursion,
-- so no need for uniform analyticity or repeated proof of all-polarization symmetry.
lemma deck_bill {I:Type}[Fintype I](n:ℕ){f:Still I}{C:ℝ}(h:Allows n f 0 C)(x:Tape n I):|Camera.deck n f x|≤C:=by
 induction n generalizing f C with
 | zero=>exact h.value
 | succ n ih=>
    let g:=wedge (x 0) f
    let L:=ContinuousLinearMap.apply ℝ ℝ (billet (x 0))
    have he:‖billet (x 0)‖≤1:=by
      apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
      intro i; unfold billet; by_cases hr:x 0=i <;> simp [hr]
    have hL: ‖L‖≤1:=by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro p; rw [one_mul];apply (p.le_opNorm _).trans _;exact mul_le_of_le_one_right (norm_nonneg _) he
    have hf:Allows n (fderiv ℝ f) 0 C:= ⟨h.analytic.fderiv_right (m:=ω) (by simp), fun k hk=>by rw [norm_iteratedFDeriv_fderiv];exact h.norm_le (k+1) (by omega)⟩
    have hh:Allows n g 0 C:=by apply (hf.linear L hL).mono (by simp)
    unfold Camera.deck;rw [abs_mul]
    have hr: |(↑n+1:ℝ)⁻¹|≤1:=by rw [abs_of_nonneg (by positivity), inv_le_one₀ (by positivity)];simp
    exact (mul_le_mul hr (ih hh (Fin.tail x)) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

-- atom coefficient estimate, empty horizon ok
def showAtom (a:Atom G n)(p:Site P): Still (Bedge G P) := fun y=>a.unmasked (offers G y) p

private lemma atoms {G:Gauge}{n N:ℕ}{P:Side}{η K:ℝ}(a:Atom G n)(u:Site P)
   (he:∀ (s:Slot)(i:G.ColorIndex),Allows N (Kiss G u s i) 0 (K*Real.exp (η*s.length))):
   Allows N (showAtom a u) 0 (a.budget η * (2^N*K)^n):=by
 let cG (k:Fin n):=K*Real.exp (η*(a.leg k).length)
 let L := ContinuousLinearMap.mul ℝ ℝ
 have hL:‖L‖≤1:=ContinuousLinearMap.opNorm_mul_le ..
 have ht(s:Finset (Fin n))(i:Tape n G.ColorIndex):Allows N (fun y=>∏ k∈s,Kiss G u (a.leg k) (i k) y) 0 (∏ k∈s,2^N*cG k):=by
   induction s using Finset.induction_on with
   | empty=>simp;exact allows_const _ (by simp)
   | insert b s hb ih=>
      simp_rw [prod_insert hb]
      have hh:= (he (a.leg b) (i b)).bilinear L ih hL
      convert hh using 1 <;> try rfl
      unfold cG;ring
 have hh:= allows_sum (s:=univ) (fun i (_:i∈(univ:Finset (Tape n G.ColorIndex)))=> (ht univ i).smul (a.coeff i))
 convert hh using 1 <;> try rfl
 unfold Atom.budget cG
 rw [← Finset.sum_mul]
 change a.magnitude*_*_ = a.magnitude*_
 rw [mul_assoc]
 apply congrArg
 simp_rw [←mul_assoc];rw [Finset.prod_mul_distrib,←Real.exp_sum,← Finset.mul_sum,Atom.length,Nat.cast_sum]; simp [mul_comm]

lemma per_atom (G:Gauge)(n N:ℕ){η:ℝ}(hp:0<η):∃ C:ℝ,1≤C∧∀ (a:Atom G n) (P:Side)(u:Site P), Allows N (showAtom a u) 0 (a.budget η * C):=by
 obtain ⟨K,hK,h⟩:=kissing G N hp
 exact ⟨(2^N*K)^n,one_le_pow₀ (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hK),fun a P u=>atoms a u (h P u)⟩

lemma per_deck (G:Gauge)(n N:ℕ){η:ℝ}(hp:0<η):∃ C:ℝ,1≤C∧∀ (a:Atom G n) (P:Side)(u:Site P)(x:Tape N (Bedge G P)),|Camera.deck N (showAtom a u) x|≤a.budget η * C:=by
 obtain ⟨C,hC,h⟩:=per_atom G n N hp
 exact ⟨_,hC,fun a P u x=>deck_bill _ (h a P u) x⟩
end YM.RG08.Carrel
