import YM.FullVolume.Nectar.Avalon
import YM.FullVolume.Nectar.Celiac
import YM.FullVolume.Nectar.Linos
/- Lattice-packing receipt passes spatial directions in μ basis.E. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Luna.Aank
open Filter Function Set MeasureTheory Push Push.AbsoluteSums RG Lattice Finset
open FullVolume.Ray Jams FullVolume.Ray.Weigh MergeProof Marker Accent
open scoped Topology ContDiff BigOperators Classical
variable {V I Y J : Type}[DecidableEq V][Fintype V][Fintype I] {B: Marker.Census V} {G:Gauge} {n:Side}
variable {F:sun→I→Y→Poly B}{q p C:ℝ} {b:ℕ}(S:I→ Support n)(v:V→ ℝ) (hv:∀ i,0<v i)
variable (k:Finset (B.Mode))(z:V→Site n)
variable [Fintype J] (f:J→I→Y→ Poly B) (c:J→ℝ)
local notation "X"=> (I→Y→Poly B)
variable (g:I→Y→Poly B)(h:g=∑ j,(c j:ℂ) • f j)
local notation "Φ"=> curtain S v k z b p
def Glacial (I E Y:Type)[NormedAddCommGroup E]: Type:= ↥(Glacier I E Y)
namespace Glacial
variable (E:Type)[NormedAddCommGroup E]
instance : NormedAddCommGroup (Glacial I E Y):= inferInstanceAs (NormedAddCommGroup (Glacier I E Y))
instance [NormedSpace ℝ E]: NormedSpace ℝ (Glacial I E Y):= by exact (inferInstanceAs (NormedSpace ℝ (Glacier I E Y)))
instance [CompleteSpace E]: CompleteSpace (Glacial I E Y):= by exact inferInstanceAs (CompleteSpace (Glacier I E Y))
def evalP [NormedSpace ℝ E](i:I)(p:Y): Glacial I E Y→L[ℝ] E:=Glacier.seesG E i p
abbrev fold {E:Type}[NormedAddCommGroup E](x:Glacier I E Y):Glacial I E Y:=x
lemma extR [NormedSpace ℝ E][CompleteSpace E]{a b:Glacial I E Y}(h:∀ i y,evalP E i y a=evalP E i y b):a=b:= Glacier.equal (f:=(show ↥(Glacier I E Y) from a)) h -- annotate
end Glacial
include h
lemma turnC (hg:Glacier.Bagged (organs S v k z b p g))(hf:∀ x,Glacier.Bagged (organs S v k z b p (f x))): Glacial.fold (Φ g)=∑ i,c i • Glacial.fold (Φ (f i)):=by
     apply Glacial.extR ℂ; intro i y; let P:=Glacial.evalP (I:=I × B.Mode) ℂ i y; change P (Glacial.fold (Φ g))= P (∑ i,c i • Glacial.fold (Φ (f i)))
     have he j:P (Glacial.fold (Φ (f j)))=organs S v k z b p (f j) i y:= Glacier.unity _ (hf j) i y
     rw [show P (Glacial.fold (Φ g))=_ from Glacier.unity _ hg i y,map_sum]; simp_rw [map_smul]; change organs S v k z b p g i y= ∑ j,c j • P (Glacial.fold (Φ (f j))); simp_rw [he]
     rw [h]; unfold organs; split_ifs; swap
     · simp
     let u:= Real.exp (p*coverNumber b (S i.fst))*Poly.toll v i.2; simp_rw [Finset.sum_apply,Poly.part_sum,Pi.smul_apply, Poly.part_smul, Finset.smul_sum]
     exact sum_congr rfl fun j _=>smul_comm u (c j) ((f j i.1 y).part i.2) -- ℝ smul instance mismatch via Complex field.
section simple
local notation "𝔈"=> Glacier I ℂ Y
variable (P:BudgetPoint)(x:B.Mode)
abbrev bright (p:ℝ)(g:X):= pack S p P (fun i y=> (g i y).part x)
abbrev shout (p:ℝ) (g:X): 𝔈:= Glacier.castle (bright S P x p g)
lemma turnS (hp: Glacier.Bagged (bright S P x p g))(hq:∀ j, Glacier.Bagged (bright S P x p (f j))) : Glacial.fold (shout S P x p g)=∑ j,c j • Glacial.fold (shout S P x p (f j)):=by
     apply Glacial.extR ℂ; intro i y
     let p':=Glacial.evalP (I:=I) ℂ i y; let Q:=(fun v:I→Y→Poly B=> Glacial.fold (shout S P x p v)); let U:=bright (Y:=Y) S P x p
     change p' (Q g)=p' (∑ j,c j • Q (f j)); have he j:p' (Q (f j))=U (f j) i y:= Glacier.unity _ (hq j) i y
     rw [show p' (Q g)=_ from Glacier.unity _ hp i y,map_sum]; simp_rw [map_smul,he]
     change U g i y = _; rw [h];unfold U bright pack
     simp_rw [Finset.sum_apply,Poly.part_sum,Pi.smul_apply, Poly.part_smul, Finset.smul_sum];
     exact sum_congr rfl fun j _=> smul_comm _ (c j) _
end simple
end YM.PhysicalNext.Repeat.Luna.Aank
