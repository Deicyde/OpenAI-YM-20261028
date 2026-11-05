import YM.FullVolume.E6.Garbs
/-! E6 Layout steps full volume.Epoch. Keep Records by exact tags.Canvas.Read.F. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Lim
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration PhysicalNext.Repeat Greenbelt Match Song Refrain
open Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open UVNext.CouplingReset Animals Progress.DirectedRecipe Ovens
open Stationary Stationary.Shade Stationary.Beacon Laurent Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {P : Teller G} {S : StepData c f} {F : Forest S.ratio}
private lemma route_size (x y : Cover) : (route x y 1).length = size (y-x) := by
  have ha : allAxes 1 = [0,1,2,3] := by decide
  simp [route, axisRoute,ha,size,Fin.sum_univ_succ,straight,Axis]
private lemma size_scaled (x : Cover) (d : ℕ) : size (d • x) = d * size x := by
  simp [size,Pi.smul_apply,Int.natAbs_mul, Finset.mul_sum]
private lemma max_lift (L : Side) (x : Site L) : size (lift x) ≤ 4 * L.val := calc
  _ ≤ ∑ _i : Axis, L.val := Finset.sum_le_sum fun i _ => by have hh := lift_centers x i; omega
  _ = _ := by simp [Axis]

private lemma contained {R : ℕ} {i : Cover} (h : size i ≤ R) : i ∈ Lattice.box R := by
  rw [box_test]
  constructor <;> intro k <;> have hh : (i k).natAbs ≤ R := (FreeResolvent.own_size i k).trans h <;> omega

lemma tagSet (k:ℕ):∃ J:Finset ℕ,∀ i,(Beacon.flag i).length≤k→i∈J:=by
    let L:Finset (PlaqAxes×Cover):= Finset.univ ×ˢ Lattice.box k
    refine ⟨L.map addresses.symm.toEmbedding,fun i hi=>?_⟩; rw [Beacon.flag,walkSlot_cost] at hi
    exact Finset.mem_map_equiv.mpr (mem_product.mpr ⟨mem_univ _,contained (by simpa only [Equiv.symm_symm] using (show size (addresses i).2 ≤ k by omega))⟩)
private lemma finite_routed (L : Side) (z : Site L) (R : ℕ) (u : Cover) (h : (route (lift z) (L.val • u) 1).length ≤ R) :
    u ∈ Lattice.box (R+4*L.val) := by
  rw [route_size] at h
  apply contained
  have hl : size u ≤ size (L.val • u) := by rw [size_scaled]; exact Nat.le_mul_of_pos_left _ L.property
  refine hl.trans ?_
  nth_rw 1 [← sub_add_cancel (L.val • u) (lift z)]
  exact (size_add ..).trans (Nat.add_le_add h (max_lift L z))
open FullVolume.Shadow
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{I: Ultrafilter ℕ}{φ:Filter ℕ}{Λ: Era G S} {K H: ℕ→ Epoch Λ}{j:ℕ}{x:E}{U V:ℕ→E→ Config G c}
-- convergence along filter, tightness from additional.
def Soul (φ:Filter ℕ)(D W:ℕ→Cad G):Prop:= (∀ i k,Glints φ (fun n=>(D n).fare i k) (fun n=>(W n).fare i k)) ∧ (∀ i k,Glints φ (fun n=> (D n).d2 i k) (fun n=> (W n).d2 i k))∧ (∀ i k,Glints φ (fun n=> (D n).d3 i k) (fun n=> (W n).d3 i k)) ∧ (∀ i k,Glints φ (fun n=> (D n).d4 i k) (fun n=> (W n).d4 i k))
structure Finish (φ:Filter ℕ)(X Y:ℕ→Epoch Λ) :Prop where
    up : Soul φ (fun i=>(X i).up) (fun i=>(Y i).up)
    down : Soul φ (fun i=>(X i).down) (fun i=>(Y i).down)
    mf : ∀ i k j,Glints φ (fun n=> (X n).R.mf i k j) (fun n=> (Y n).R.mf i k j)
    mn : ∀ i k j,Glints φ (fun n=> (X n).R.mn i k j) (fun n=> (Y n).R.mn i k j)
    o : ∀ i k j,Glints φ (fun n=> (X n).R.o i k j) (fun n=> (Y n).R.o i k j)
    beta: Glints φ (fun n=> (X n).beta) (fun n=> (Y n).beta)
    price:∀ l,∀ V:ℕ→ Config G f, Glints φ (fun n=> (X n).kin.activities.regularOccurrence Λ.p l (V n)) (fun n=> (Y n).kin.activities.regularOccurrence Λ.p l (V n))
    grant:∀ l,∀ V:ℕ→ Config G f, Glints φ (fun n=> (X n).k l (V n)) (fun n=> (Y n).k l (V n))
variable {D W:ℕ→ Cad G}{k d:ℕ}
lemma Soul.stain (h:Soul φ D W)(r:Clip)(hd:0<d)(hv:Quincy φ j x U V)(t:Twin c)(k) : Frill φ j x (fun n y=> plotted (D n).path r k d (U n y) t) (fun n y=> plotted (W n).path r k d (V n y) t) :=by
    rcases t with ⟨t,h'|h'⟩
    · exact (Frill.still _).fee (hv.pores t|>.songs)
    obtain ⟨T,hT⟩:= tagSet k
    have he (M:Cad G) (V:Config G c): plotted M.path r k d V (t,true)=∑ i∈T,shortenTerm M.path k d V t i:=by
        refine tsum_eq_sum fun i hi=> if_neg fun h=>hi (hT i ?_)
        exact (Nat.le_mul_of_pos_right _ hd).trans h
    simp_rw [he]; refine Frill.buds T fun i hi=>?_
    by_cases hh:(Beacon.flag i).length * d ≤ k
    · simp only [Cad.path,shortenTerm,hh,↓reduceIte]; exact (Frill.bare (h.1 t.2 i)).fee (hv.atspot _ _)
    simp only [Cad.path, shortenTerm,hh,↓reduceIte]; exact Frill.still _
namespace Finish
variable (h:Finish φ K H) (hx:Quincy φ j x U V)
include h hx
lemma taps (u v k) : Frill φ j x (fun n y=> (K n).tubes.Φ k (U n y) u v) (fun n y=> (H n).tubes.Φ k (V n y) u v):=by
    let A:= S.patch.L; let T:= Lattice.box (k+4*A.val); let P:= (mesh u); let Q:= (mesh v)
    have ha R V : Tube.Φ (G:=G) (S:=S) R k V u v=∑ i∈ T,casted S R.R k V P Q i:=tsum_eq_sum fun i hi=> if_neg fun h=>hi (finite_routed _ _ _ _ h.1)
    simp_rw [ha]; apply Frill.buds T; intro i _
    let w:= route (lift (S.ratio.residue P.1)) (S.patch.L.val • i) 1
    by_cases hi:w.length ≤ k ∧ Q.1=S.ratio.parent P.1+wrap c i
    · dsimp only [w] at hi; simp only [casted,hi,↓reduceIte]; exact (Frill.bare (h.mf _ _ _)).fee ((hx.books S).weft _ _|>.nupt)
    dsimp only [w] at hi; simp only [casted,hi,↓reduceIte]; exact Frill.still _
omit h in
private lemma peeks {α β:Type} (M N:ℕ→ Row α β)(hd:0<d)(he:∀ i j w, Glints φ (fun l=> M l i j w) (fun l=>N l i j w))(k v w): Frill φ j x (fun n y=> lane k d (U n y) (M n) v w) (fun n y=> lane k d (V n y) (N n) v w):=by
    have hp U F : lane k d (G:=G) U F v w=∑ i∈Lattice.box k, Pressure.priced k d U F v w i:=by
        refine tsum_eq_sum fun i hi=> if_neg fun h=>hi (contained ?_)
        have he: (route 0 i 1).length ≤ k:= (Nat.le_mul_of_pos_right _ hd).trans h.1
        simpa only [route_size,sub_zero] using he
    simp_rw [hp]; apply Frill.buds _; intro i _
    by_cases hl:(route 0 i 1).length*d≤k ∧ w.1=v.1+wrap c i
    · simp only [Pressure.priced,hl,↓reduceIte]; exact (Frill.bare (he _ _ _)).fee (hx.weft _ _|>.nupt)
    simp only [Pressure.priced,hl,↓reduceIte]; exact Frill.still _
include h
lemma toes (u v k) : Frill φ j x (fun n y=> (K n).tubes.Φ' k (U n y) u v) (fun n y=> (H n).tubes.Φ' k (V n y) u v):= peeks hx _ _ S.patch.L.property h.mn ..
lemma boots (u v k) : Frill φ j x (fun n y=> (K n).tubes.N k (U n y) u v) (fun n y=> (H n).tubes.N k (V n y) u v):= peeks hx _ _ S.patch.L.property h.o ..
end Finish
end YM.ConnectedActivityE6.Lim
