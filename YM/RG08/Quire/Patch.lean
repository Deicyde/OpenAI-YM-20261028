import YM.RG08.Quire.Clasp

/-! # Exact collapses before period release -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Quire
open RG Laurent Lattice Wilson Bloch Next.Free Work.F08 Push.AbsoluteSums Finset Function Filter Matrix Analysis
open UVExt.Paths Stationary
open scoped Topology ContDiff BigOperators
variable {α β ι : Type} [Fintype α] [DecidableEq α] {p : Option Side} {r s : ℕ} {K H : Row α α} {m : Side}
variable {U : Rooted ℝ α (r+1)} {F : Rooted ℝ α (r+2)} {V : Shale α (s+1)}
omit [DecidableEq α] in
lemma st_tub (v : Fin r→PAC α m) (f : β →ℝ) (hp : Pens f) (k : β→Beads α r) (z : Site m) :
    stitch (tub f k) m z v=∑' j,f j*rosary v z (k j) := (stitch_apply ((hp.pours k).of_norm) v z).trans (pool_total _ k hp.of_norm (rosary_bill v z))
private def soak (i j : Co m α) (x : PAC α m) : Fin (r+2) → PAC α m := Fin.cons (zpk i) (Fin.cons (zpk j) (fun _=>x))
private lemma noon (b : Beads α (r+2)) (z : Site m) (x : PAC α m) :
    (∑ i,∑ j, K.acts m i j*(F b*rosary (soak i j x) z b))=
        knot (.some m) F K b*rosary (fun _=>x) z (stems b) := by
  let u := silks z b 0; let v := silks z b (Fin.succ (0:Fin _))
  rw [sum_eq_single u,sum_eq_single v]; swap
  · intro j _ hj; unfold rosary soak; rw [Fin.prod_univ_succ,Fin.prod_univ_succ]
    change _*(F b*(_*((zpk j v)*_)))=_; rw [show zpk j v=0 from Pi.single_eq_of_ne hj.symm _]; ring
  swap; · simp
  swap
  · intro j _ hj; apply sum_eq_zero; intro i _; unfold rosary soak; rw [Fin.prod_univ_succ]; change _*(F b*(zpk j u *_))=_; rw [show zpk j u=0 from Pi.single_eq_of_ne hj.symm _]; ring
  swap; · simp
  unfold rosary soak; rw [Fin.prod_univ_succ,Fin.prod_univ_succ]; simp only [Fin.cons_zero,Fin.cons_succ,u,v,zpk,Pi.single_eq_same,one_mul]
  rw [knot,tuneS,stroke_trans K _ _ _ z]; unfold silks; rw [←mul_assoc]; rfl
lemma root_lap (h : Tidy F) (hp : Whole K) (m : Side) (o : Site m) :
    lap (K.acts m) (rootSong F m o) = rootSong (jib (some m) K F) m o := by
  have hs := h.pens.of_norm; have he := knot_prices h.pens hp (some m)
  rw [jib,sew_diagonal (he.pours stems|>.scale _),rootSong,rootSong,st_scale _ (he.pours _|>.of_norm)] -- wrong rootSong unfolds
  funext x
  change lap _ (Tensor.diagonal (stitch F m o)) x=(batting r:ℝ)*stitch _ m o _
  rw [st_tub _ _ he stems]
  have hx (i j : Co m α) : Analysis.D (zpk j) (D (zpk i) (Tensor.diagonal (stitch F m o))) x =
      ((↑(r+2:ℕ):ℝ)*(↑(r+1:ℕ):ℝ))*stitch F m o (soak i j x) := DDfade (zpk i) (zpk j) _ (h.sym _) _
  simp_rw [lap,hx,mul_left_comm (K.acts m _ _)]; simp_rw [← Finset.mul_sum]; rw [← mul_assoc, ← mul_assoc _ (↑(r+2:ℕ):ℝ)]
  rw [show ((1/2:ℝ)*↑(r+2:ℕ)*↑(r+1:ℕ))=batting r by push_cast; rfl]; congr 1
  let G i j (b:Beads α (r+2)) := K.acts m i j*(F b*rosary (soak i j x) o b)
  have hg i j : Summable (G i j) := (bead_summable _ _ hs _).mul_left _
  simp_rw [stitch_apply hs,← tsum_mul_left]; change (∑ i,∑ j,∑' b,G i j b)=_
  simp_rw [← Summable.tsum_finsetSum (fun j _=> hg _ j)]
  rw [← Summable.tsum_finsetSum (s:=univ) (fun i _=> summable_sum (s:=univ) fun j _=> hg i j)]
  exact tsum_congr fun b=> noon ..

private def tapU (i : Co m α) (x : PAC α m) : Fin (r+1)→PAC α m := Fin.cons (zpk i) (fun _ => x)
private def drink (U : Shale α (r+1)) (x : PAC α m) (z : Site m) (b : Beads α (r+1)) (i : Co m α) :=
    U b*rosary (tapU i x) z b
private lemma ever (U : Shale α (r+1)) (x : PAC α m) (z : Site m) (b : Beads α (r+1)) (i : Co m α) :
    drink U x z b i = if silks z b 0=i then U b*rosary (fun _=>x) z (stem1 b) else 0 := by
  unfold drink rosary tapU; rw [Fin.prod_univ_succ]; simp only [Fin.cons_zero,Fin.cons_succ,zpk,Pi.single_apply]; split <;> simp_all; left; rfl
private lemma nerve (V : Shale α (s+1)) (x : PAC α m) (z : Site m) (b : Beads α (s+1)) (i : Co m α) (h : ordered V) : drink V x z b i= if (z,(b 0).2)=i then V b*rosary (fun _=>x) z (stem1 b) else 0 := by
  rw [ever V]; by_cases hx : V b=0
  · simp [hx]
  rw [show silks z b 0=(z,(b 0).2) from by unfold silks; rw [show (b 0).1=0 from h b hx,map_zero,add_zero]]
omit [DecidableEq α] in
private lemma board (x : PAC α m) (z : Site m) (i : Coves α r s × Cover) :
    let b:=i.1.1; let p:=i.1.2;
    sires (stemLayer U V) (wakes K) i * rosary (fun _=>x) z (coral i)=
    K (b 0).2 (p 0).2 i.2*((U b*rosary (fun _=>x) z (stem1 b)) * (V p*rosary (fun _=>x) ((silks z b 0).1+wrap m i.2) (stem1 p))) := by
  intro b p; unfold coral tide rosary; rw [Fin.prod_univ_add]; simp only [silks, Fin.append_left,Fin.append_right,shiftedBy,map_add]
  have he (j : Fin s) : z+ (wrap m ((stem1 p j).1)+(wrap m (b 0).1+wrap m i.2))=(z+wrap m (b 0).1+wrap m i.2)+ wrap m (stem1 p j).1 := by abel
  unfold p b at *; simp_rw [he]; unfold sires stemLayer wakes; simp only [smul_eq_mul]; ring
private lemma maps_at (x : PAC α m) (o z : Site m) (b : Beads α (r+1)) (c : Beads α (s+1)) (h : Tunable V) :
    (∑ i,∑ j, K.acts m i j*(drink U x o b i*drink V x z c j))=
     K.acts m (silks o b 0) (z,(c 0).2) * ((U b*rosary (fun _=>x) o (stem1 b)) *(V c*rosary (fun _=>x) z (stem1 c))) := by
  simp_rw [ever U, nerve V _ _ _ _ h.2.1]
  rw [sum_eq_single (silks o b 0),if_pos rfl,sum_eq_single (z,(c 0).2),if_pos rfl]
  · intro j _ hj; simp [Ne.symm hj]
  · simp
  · intro j _ hj; simp [Ne.symm hj]
  simp
private lemma dusk (x : PAC α m) (o : Site m) (b : Coves α r s) (h : Whole K) (ht : Tunable V) :
    (∑' j:Cover, sires (stemLayer U V) (wakes K) (b,j) * rosary (fun _=>x) o (coral (b,j)))=
      ∑ z:Site m, ∑ i,∑ j,K.acts m i j*(drink U x o b.1 i*drink V x z b.2 j) := by
  simp_rw [maps_at _ _ _ _ _ ht, board]
  exact (sift_action (h.safe _ _).of_norm m (silks o b.1 0).1 (fun y=> (_*rosary (fun _:Fin r=>x) o _) * (_*rosary (fun _:Fin s=>x) y _))).symm

private lemma chorus (h : Tidy U) (g : Tunable V) (k : Whole K) (m : Side) (o : Site m) (x : PAC α m) :
    (∑ i:Co m α,∑ j:Co m α,K.acts m i j*(stitch U m o (tapU i x)*recital V m (tapU j x)))=
      ∑' b,sires (stemLayer U V) (wakes K) b*rosary (fun _=>x) o (coral b) := by
  let Q i j z (b:Coves α r s) := K.acts m i j*(drink U x o b.1 i * drink V x z b.2 j)
  have hc (i j : Co m α) (z : Site m) : Summable (Q i j z) := (summable_mul_of_summable_norm (bead_summable U (tapU i x) h.pens.of_norm o).norm (bead_summable V (tapU j x) g.1 z).norm).mul_left _
  have he (i j : Co m α) : K.acts m i j * (stitch U m o (tapU i x)* recital V m (tapU j x))=∑ z,∑' p,Q i j z p := by
    rw [stitch_apply (h.pens.of_norm),recital_eval (tapU j x) g.1,Finset.mul_sum,Finset.mul_sum]; refine sum_congr rfl fun z _=>?_; rw [tsum_mul_tsum_of_summable_norm (bead_summable U (tapU i x) h.pens.of_norm o).norm (bead_summable V (tapU j x) g.1 z).norm,←tsum_mul_left]; rfl
  let P : Coves α r s × Cover→ℝ := sires (stemLayer U V) (wakes K)
  let S i := P i * rosary (fun _:Fin (r+s)=> x) o (coral i)
  have hx : Summable S := sum_bounded (show Summable P from (coral_pens h.pens g.1 k).of_norm) (g:=fun i=> rosary (fun _:Fin (r+s)=> x) o (coral i)) (fun i=> rosary_bill (fun _:Fin (r+s)=>x) o (coral i))
  have hv i j : (∑ z,∑' p,Q i j z p)=∑' p,∑ z, Q i j z p := (Summable.tsum_finsetSum (fun z _=>hc i j z)).symm
  have hE i : (∑ j, ∑' p,∑ z, Q i j z p)=∑' p,∑ j,∑ z,Q i j z p := (Summable.tsum_finsetSum (fun j _=>summable_sum (s:=univ) (fun z _=>hc i j z))).symm
  simp_rw [he,hv,hE]
  change _=∑' i, S i
  rw [← Summable.tsum_finsetSum (s:=univ) (fun i _=> summable_sum (s:=univ) fun j _=> summable_sum (s:=univ) fun z _=>hc i j z), hx.tsum_prod]
  apply tsum_congr; intro b
  have hw : (∑' i:Cover, S (b,i))=∑ z,∑ i,∑ j, Q i j z b := dusk x o b k g
  rw [hw]; have hp (i : Co m α) : ∑ j:Co m α,∑ z:Site m,Q i j z b=∑ z:Site m,∑ j:Co m α,Q i j z b := Finset.sum_comm
  simp_rw [hp]; exact Finset.sum_comm
set_option maxHeartbeats 320000 in
lemma clasp_love (h : Tidy U) (g : Tunable V) (k : Whole K) (m : Side) (o : Site m) :
    arch (K.acts m) (rootSong U m o) (stanza V m)=rootSong (clasp K U V) m o := by
  have hm := tie_pens h.pens g.1 k
  rw [clasp,sew_diagonal (hm.scale (syl r s)),rootSong,rootSong,st_scale _ hm.of_norm]
  funext x
  change arch (K.acts m) (Tensor.diagonal (stitch U m o)) (stanza V m) x=(syl r s:ℝ)*stitch (tie U V K) m o (fun _=>x)
  unfold tie; rw [st_tub _ _ (coral_pens h.pens g.1 k)]
  have hy (i j : Co m α) : K.acts m i j * D (zpk i) (Tensor.diagonal (stitch U m o)) x * D (zpk j) (stanza V m) x =syl r s*(K.acts m i j*(stitch U m o (tapU i x)*recital V m (tapU j x))) := by
    unfold stanza; rw [Dfade _ _ (h.sym _),Dfade _ _ (g.2.2 m)]; simp only [Pi.smul_apply, Tensor.diagonal,ContinuousMultilinearMap.curryLeft_apply]; unfold syl tapU; simp only [smul_eq_mul]; ring
  simp_rw [arch,hy,← Finset.mul_sum]; congr 1
  exact chorus h g k m o x
end YM.RG08.Quire
