import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Hood
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.JacF

/-! # Root-change integer unimodularity on full measure space -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.TreeColor
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Bid  Packets
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} (F H : Forest S.ratio) (t : (↥F.trunks)≃↥H.trunks)
variable (A : Type) [CommRing A]

def shifts (v : Tubular f G → A) : Tubular f G → A := fun i=> surgery F H t (fun j=> v (j,i.2)) i.1
private lemma sc_mul (a:A) (u : Bond f → A) : bundled F (a • u)=a • bundled F u := by
  have he x w:linkSum (a • u) x w=a • linkSum u x w := by
    induction w generalizing x with
    | nil => simp [linkSum]
    | cons d w ih=> rw [linkSum,linkSum,ih]; split <;> simp [*,mul_add]
  unfold bundled aligns; simp_rw [he]; funext i; simp only [gradient,Pi.add_apply,Pi.smul_apply]; module

def scaleMatrix (G : Gauge) : Matrix (Tubular f G) (Tubular f G) A := LinearMap.toMatrix' (show Module.End A (Tubular f G → A) from
    { toFun := shifts F H t A
      map_add' a b := by
        funext i; let u j:= a (j,i.snd); let v j:=b (j,i.snd); unfold shifts surgery; rw [Pi.add_apply]; split <;> rename_i h
        · rfl
        have he : directF F (u+v)=directF F u+directF F v:= by funext i; unfold directF; rw [Pi.add_apply]; split <;> simp_all
        change bundled H (directF F (u+v)) i.1=_; rw [he,bundle_sum]; rfl
      map_smul' a b := by
        funext i; let u j:= b (j,i.snd); unfold shifts surgery; rw [Pi.smul_apply]; split <;> rename_i h
        · rfl
        have he : directF F (a • u)=a • directF F u:= by funext i; unfold directF; rw [Pi.smul_apply]; split <;> simp_all
        change bundled H (directF F (a • u)) i.1=_; rw [he,sc_mul]; rfl })
lemma consents (a : Tubular f G → A) : scaleMatrix F H t A G *ᵥ a=shifts F H t A a := by unfold scaleMatrix; rw [LinearMap.toMatrix'_mulVec]; rfl
lemma receives (G : Gauge) : scaleMatrix F H t A G*scaleMatrix H F t.symm A G=1 := by
  apply Matrix.toLin'.injective; apply LinearMap.ext; intro a; change _ *ᵥ a=(1:Matrix ..) *ᵥ a
  rw [← Matrix.mulVec_mulVec, consents,consents,Matrix.one_mulVec]; funext i
  exact congr_fun (stays_all H F t.symm (fun j=> a (j,i.2))) i.1

variable {W : Type} [AddCommGroup W] {V : Type} [AddCommGroup V]
omit [CommRing A]
lemma add_transport (v : Bond f → W) (L : W→+V) : surgery F H t (L ∘ v)=L ∘ surgery F H t v := by
  have he (x : Site f) p (u: Bond f→ W): linkSum (L ∘ u) x p = L (linkSum u x p) := by
    induction p generalizing x with
    | nil => simp [linkSum]
    | cons d p ih => rw [linkSum,linkSum,ih]; split <;> simp [*]
  have hp : directF F (L ∘ v) = L ∘ directF F v := by funext i; unfold directF; rw [Function.comp_apply]; split <;> simp_all
  funext i; unfold surgery; rw [Function.comp_apply]; split <;> rename_i h
  · rfl
  rw [hp]; unfold bundled aligns gradient; simp only [he, Function.comp_apply, Pi.add_apply,map_add,map_sub]

lemma no_mas (G : Gauge) : |(scaleMatrix F H t ℝ G).det|=1 := by
  let A:= scaleMatrix F H t ℤ G; let B:= scaleMatrix F H t ℝ G
  have hp : |A.det|=1:= Int.isUnit_iff_abs_eq.mp (Matrix.isUnit_det_of_right_inverse (receives F H t ℤ G))
  let f' := Int.castRingHom ℝ
  have he : B=(f'.mapMatrix) A := by
    ext i j; change B i j=f' (A i j)
    let e: Tubular f G→ℤ := Pi.single j 1
    let v: Tubular f G→ℝ := Pi.single j 1
    have hz : v=f' ∘ e := by funext k; simp [e,v,Pi.single_apply]
    have ha : ((B *ᵥ v) i)=B i j := congr_fun (Matrix.mulVec_single_one B j) i
    have hb : ((A *ᵥ e) i)=A i j := congr_fun (Matrix.mulVec_single_one A j) i
    rw [← ha, ← hb,hz,consents F H,consents F H]
    exact congr_fun (add_transport F H t (fun k=> e (k,i.2)) f'.toAddMonoidHom) i.1
  rw [show scaleMatrix F H t ℝ G=B from rfl,he,← RingHom.map_det f' A]; change |(A.det:ℝ)|=1; exact_mod_cast hp
end YM.ConnectedActivityE6.TreeColor
