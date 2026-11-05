import YM.Euclid.RPPeak
import YM.Extraction.Pairs


/-!
# Obtain full Euclidean-positive hierarchy, conditional on through-ties

Parallel passage pin. Positivity uses true-Wilson normalized measure both
orders, terminal columns real-signed. Nothing on tilted planes assumed at cutoffs
beyond discrete symmetries.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extraction.Order
open Function Filter Set MeasureTheory Wilson Cells Lattice
open Table Table.Pairing Banks
open scoped Topology BigOperators ComplexOrder Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Order}

private lemma posVectors {n : Side} {p : Cut n} {β} (h : Positive G β p) (m) (W : Fin m → Config G n → ℂ) (e : Fin m→ℂ)
    (ht : ∀ i, Interior p.sector (W i)) :
    0 ≤ ∑ i, ∑ j, star (e i) * e j * form β p (W j) (W i) := by
  classical
  let Y i (U) := e i*W i U
  let T (s : Finset (Fin m)) := fun U => ∑ i∈s,Y i U
  have hv i : Interior p.sector (Y i) := Interior.scale (e i) (ht i)
  have hp (s) : Interior p.sector (T s) := by
    induction s using Finset.induction_on with
    | empty => unfold T; simp only [Finset.sum_empty]; exact Interior.constant _ _
    | @insert i s hi ih => unfold T; simp_rw [Finset.sum_insert hi]; exact (hv i).plus ih
  have hh (s : Finset (Fin m)) (V : Config G n → ℂ) (hV : Interior p.sector V) :
      form β p (T s) V=∑ i∈s, e i * form β p (W i) V := by
    induction s using Finset.induction_on with
    | empty => simp [form,moment,T]
    | @insert i s hi ih =>
      rw [show T (insert i s)=(fun x => Y i x+T s x) by simp [T,Finset.sum_insert hi],plusF (hv i) (hp s) hV,scaleF,ih,Finset.sum_insert hi]
  let s : Finset (Fin m) := Finset.univ
  have he i : form β p (W i) (T s)=∑ j, star (e j)*form β p (W i) (W j) := by
    rw [exchange (ht i) (hp s), hh s _ (ht i)]; simp only [star_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [star_mul',← exchange (ht i) (ht j)]
  have hm : 0≤form β p (T s) (T s) := h (T s) (hp s)
  rw [hh s _ (hp s)] at hm
  rw [Finset.sum_comm]; simp_rw [he,Finset.mul_sum] at hm
  simpa only [s,mul_left_comm,mul_comm,mul_assoc] using hm

theorem realPositive (H : f.Ordered C S) (hp : C.Makes) (hd : S.Symmetric) (hx : S.Smooth) : S.RPSmear := by
  refine ⟨fun _ a b => pairedIntegrable S hd hx a b,fun a n v c => ?_⟩
  simp_rw [← at_integral S hd hx]
  apply ge_of_tendsto (tendsto_finsetSum _ (fun i _ => tendsto_finsetSum _ (fun j _ =>
    ((H.reads _ (tied (v i).v (v j).v a) (withOther (v i) (v j)) |> along).const_mul _))))
  let k := plane C
  have hh (i) : ∀ᶠ j in f.fuse, supported C (v i) j.2 := by
    rw [fused]
    exact (f.per.cofinal.eventually (reading C.S (v i).f)).mono fun _ hi => Eventually.of_forall fun _ => hi
  filter_upwards [eventually_all.mpr hh, eventually_all.mpr (fun i => witnesses (v i).v f),
    eventually_all.mpr (fun i => kept C hp f (v i))] with x hy he hs
  obtain ⟨N,p⟩ := x
  have hh i j := at_cut C (N := N) (v i) (v j) (he i) (hy i) hp
  simp only; simp_rw [hh]
  exact posVectors ((seamless hp N p).positive _) n (fun i => stem C (v i) N p) c hs

theorem assembles (H : f.Ordered C S) (hu : f.PointLimits C S) (hp : C.Makes) (h : S.Smooth) (hc : S.Capped) : S.Hierarchy := by
  let x := limits_basic hp h hu
  have ht := realPositive H hp x.toSymmetric h
  exact ⟨x, spin hp h hu, homogeneous hp h hu, at_point x.toSymmetric h ht, ht,h,hc⟩
end YM.Extraction.Order
