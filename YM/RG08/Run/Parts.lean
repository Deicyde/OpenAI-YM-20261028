import YM.RG08.Run.Halo
/-!
# Single-frame motion through polymer/tensor edge, in kme. No estimate of masks. Unconditional exponential† supplied for canonical data; here polymer consumers throughout *finite* any depth.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Run
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door
open scoped BigOperators Topology Real ContDiff Classical
variable {I:Type}{G:Gauge}{E e r d τ D j t i k m l n s :ℕ}{L:I→Side}{y v η δ w ρ:I→ℝ}{R:ℝ}{P Q:∀ i,StripU G (L i)}{U V:I→BoardU D R G}
structure LensP (k E τ:ℕ)(y δ w:I→ℝ)(P Q:∀ i,StripU G (L i)) : Prop where
  one : ∀ i, Fair (P i)
  two : ∀ i, Fair (Q i)
  age : Audience y
  pay : Weighed y (fun i=> ((L i).val:ℝ))
  art : RowBoth y δ (fun i=>(P i).cv) (fun i=>(Q i).cv) w
  meanT : RowBoth y δ (fun i=>(P i).tree) (fun i=>(Q i).tree) w
  chargesG : ∀ e≤E,∀ t≤windows τ E,∀ r,Both y δ (fun i=> Refrain (veiled (P i).cv) (P i).song none t e r) (fun i=> Refrain (veiled (Q i).cv) (Q i).song none t e r) w
  scaleT : ∀ e≤ E, Lease y δ (fun i=> PowerSeries.coeff e (P i).scale) (fun i=> PowerSeries.coeff e (Q i).scale)
  pos : ∀ i,0<w i
  owns: Weighed y (fun i=>utter k (w i))
  rent: 0 ≤ δ
lemma quarter (he : LensP k E τ y δ w P Q)(hp : ∀ i,Fits t (U i))(hg:∀ i,Fits t (V i))(hh:∀ i j k,Tidy (U i j k))(hN:∀ i j k,Tidy (V i j k))(h:t ≤ τ)(hv:1/2≤R)(hz:e ≤ E)(hδ:0 ≤ v)(hX:v≤1)(hx:∀ i,v i/(L i).val ≤ η i)
 (ht : ∀ i j, awaits 1 e r i j→ Drum k y δ ρ (fun t=> U t i j) (fun t=> V t i j) η) : Drum k y δ ρ (fun i=>halfP (P i) t d (U i) e r) (fun i=>halfP (Q i) t d (V i) e r) v := by
   have hP:= veil_contract he.art he.rent
   have hQ:= scanned_contract he.meanT le_rfl he.age he.rent
   have hU i := creamy d (L i) (hp i) (fun j k=>(hh i j k).pens) hv (he.one i).odds
   have hY i:= creamy d (L i) (hg i) (fun j k=> (hN i j k).pens) hv (he.two i).odds
   refine marks_pair ?_ hδ hX he.pos (Weighed.constant _ (Nat.cast_nonneg (Fintype.card (Loc G 1)))) he.owns he.age hQ he.rent
   unfold halfU; apply Drum.group _ he.age hδ; intro j hj
   refine aurora he.age he.pos he.rent hP (fun i=>(he.one i).lived) (fun i=>(he.two i).lived) (fun i=>(hU i).2) (fun i=>(hY i).2) (fun i=>(he.one i).tune) (fun i=>(he.two i).tune) (fun m hm j' hj' k=> he.chargesG _ (hj'.trans hz) _ (by have ht:=mem_range.mp hj; unfold windows at *; omega) k) hδ hX he.owns fun i k' hp=> wing_drum (ht i k' (by simpa only [awaits,Nat.add_one_ne_zero,one_ne_zero,↓reduceIte] using hp)) hv (fun i=> (he.one i).odds) hδ hX hx he.age he.pay
lemma inlet (he: LensP k E τ y δ w P Q)(hp:∀ i,Marvel t (U i))(hg:∀ i,Marvel t (V i))(hv:1/2≤R)(hδ:0≤v)(hX:v≤1)(hx:∀ i,v i/(L i).val≤η i)(hZ : Drum k y δ ρ (fun i=> U i e r) (fun i=> V i e r) η) : Drum k y δ ρ (fun i=> aboard d (P i).tree (U i e r)) (fun i=> aboard d (Q i).tree (V i e r)) v := by
   have hh:= marks_pair (wing_drum (t:=d) hZ hv (fun i=>(he.one i).odds) hδ hX hx he.age he.pay) hδ hX he.pos (Weighed.constant _ (Nat.cast_nonneg (Fintype.card (Loc G 1)))) he.owns he.age (scanned_contract he.meanT le_rfl he.age he.rent) he.rent
   simp_rw [fun i=>arise (P i).tree (he.one i).ct (he.one i).odds hv (U i) t (hp i).cap (hp i).hem e r d, fun i=> arise (Q i).tree (he.two i).ct (he.two i).odds hv (V i) t (hg i).cap (hg i).hem e r d] at hh; exact hh
lemma form_c (he: LensP k E τ y δ w P Q)(hp:∀ i,Marvel t (U i))(hg:∀ i,Marvel t (V i))(h:t ≤ τ)(hv:1/2≤R)(hz:e≤ E)(hδ:0≤v)(hX:v≤1)(hx:∀ i,v i/(L i).val≤η i)(hZ: ∀ i j, awaits 0 e r i j→ Drum k y δ ρ (fun t=> U t i j) (fun t=> V t i j) η): Drum k y δ ρ (fun i=>juice (P i) t d (U i) e r) (fun i=> juice (Q i) t d (V i) e r) v:= by
   unfold juice; simp_rw [fun i=> opening (he.one i).cm (he.one i).ct (hp i).hem (hp i).cap hv (he.one i).odds (he.one i).tune (he.one i).lived,fun i=>opening (he.two i).cm (he.two i).ct (hg i).hem (hg i).cap hv (he.two i).odds (he.two i).tune (he.two i).lived]
   have hh : Drum k y δ ρ (fun i=> halfP (P i) t d (U i) e r) (fun i=> halfP (Q i) t d (V i) e r) v:= quarter he (fun i=>(hp i).cap) (fun i=> (hg i).cap) (fun i=>(hp i).hem) (fun i=>(hg i).hem) h hv hz hδ hX hx (fun i j hh=>hZ i j (by unfold awaits at *; split_ifs at * <;> omega))
   exact (inlet (d:=d) he hp hg hv hδ hX hx (hZ e r (by simp [awaits]))).more hh hδ he.age
lemma foc_ear (he: LensP k E τ y δ w P Q)(hp:∀ i,Marvel t (U i))(hg:∀ i,Marvel t (V i))(h:t ≤ τ)(hv:1/2≤R)(hz:e≤ E)(hδ:0≤v)(hX:v≤1)(hx:∀ i,v i/(L i).val≤η i)(hy:0≤ρ)(hZ:∀ i j, awaits 1 e r i j→ Drum k y δ ρ (fun t=> U t i j) (fun t=> V t i j) η): Drum k y δ ρ (fun i=>fetchU (P i) t d (U i) e r) (fun i=>fetchU (Q i) t d (V i) e r) v:= by
   have hh:= quarter (d:=d) he (fun i=>(hp i).cap) (fun i=>(hg i).cap) (fun i=>(hp i).hem) (fun i=>(hg i).hem) h hv hz hδ hX hx hZ
   unfold fetchU; refine hh.more (A:=fun i=> _) (B:=fun i=>_) (Drum.group _ he.age hδ (F:=fun j i=> glaze (P i).scale r j (e-j) •_) (H:=fun j i=> glaze (Q i).scale r j (e-j) •_) (fun b hb=>?_)) hδ he.age
   have ht:= mem_range.mp hb; refine (form_c he hp hg h hv (by omega:b ≤ E) hδ hX hx (r:=r) (d:=d) (fun i j hb=>hZ i j (Or.inl (by unfold awaits at hb; omega)))).sc (rehearseT he.age (e:=e-b) (fun i hi=> he.scaleT i (by omega)) (fun i=>(he.one i).once) (fun i=>(he.two i).once) _ _) hy he.age hδ
end YM.RG08.Run
