import YM.RG08.Pivot.Fatum

set_option autoImplicit false
noncomputable section
namespace YM.RG08.Pivot
open Function Filter Lattice Wilson RG Exterior Precision Next.Free
open Laurent Bloch Matrix Work.F08 Tree FreeResolvent Stationary
open UVExt.Paths Drift Scores Loom Shade Quire Tall Vale Analysis Finset
open scoped Topology BigOperators Classical
variable {α E : Type} [Fintype α][DecidableEq α] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {U: Spine E α} {K: Row α α} {A:ℝ} {c:Side} {n k r:ℕ}
-- $\gamma_g$ Implicit KK at period
private def soar (i j : Co c α) (x : PAC α c) : Fin (r+2) → PAC α c := Fin.cons (zpk i) (Fin.cons (zpk j) (fun _:Fin r=>x))
private lemma soaking (f : Shale α (r+2)) (M : Matrix (Co c α) (Co c α) ℝ) (o : Site c) (x : PAC α c) (b : Beads α (r+2))
    (h: tuneS K none b=M (silks o b 0) (silks o b (Fin.succ (0:Fin _)))) :
    (∑ i, ∑ j,M i j *(f b*rosary (soar i j x) o b))= knot none f K b * rosary (fun _=> x) o (stems b) := by
  let u := silks o b 0; let v:= silks o b (Fin.succ (0:Fin _)); rw [sum_eq_single u,sum_eq_single v]; swap
  · intro j _ hj; unfold rosary soar; rw [Fin.prod_univ_succ, Fin.prod_univ_succ]; change _*(f b * (_*(zpk j v*_)))=_
    rw [show zpk j v=0 from Pi.single_eq_of_ne hj.symm _]; ring
  swap; · simp
  swap
  · intro j _ hj; apply sum_eq_zero; intro z _; unfold rosary soar; rw [Fin.prod_univ_succ]; change _*(f b*(zpk j u*_))=_; rw [show zpk j u=0 from Pi.single_eq_of_ne hj.symm _]; ring
  swap; · simp
  rw [knot,h]; unfold rosary soar; rw [Fin.prod_univ_succ,Fin.prod_univ_succ]; simp only [Fin.cons_zero,Fin.cons_succ,zpk,u,v,Pi.single_eq_same,one_mul,smul_eq_mul]; rw [←mul_assoc]; rfl
lemma fil_knots {f: Shale α (r+2)} (h : Tidy f) (B : Plaque K A) (o:Site c) (M:Matrix (Co c α) (Co c α) ℝ)
    (hp: ∀ b : Beads α (r+2),tuneS K none b=M (silks o b 0) (silks o b (Fin.succ (0:Fin _)))) :
    stitch (jib none K f) c o=bur M (stitch f c o) := by
  apply Tensor.ext_diag _ _ ((disciples f h.pens B).sym o) (bur_sym _ (h.sym _))
  have he:= Fink_tap B h.pens; funext x; change rootSong (jib none K f) _ _ _= _
  rw [jib, sew_diagonal (he.pours stems|>.scale _),rootSong,st_scale _ (he.pours stems|>.of_norm)]
  unfold Tensor.diagonal; rw [_root_.smul_apply,smul_eq_mul,bur_eval]
  congr 1; rw [st_tub _ _ he]
  let g i j (b : Beads α (r+2)):= M i j *(f b*rosary (soar i j x) o b)
  have hg i j : Summable (g i j):= (bead_summable f (soar i j x) h.pens.of_norm o).mul_left _
  simp_rw [stitch_apply h.pens.of_norm,← tsum_mul_left]; change _=∑ i,∑ j,∑' b,g i j b
  simp_rw [← Summable.tsum_finsetSum (f:=fun j (b:Beads α (r+2))=> g _ j b) (s:=univ) (fun j _=> hg _ j)]  
  rw [← Summable.tsum_finsetSum (s:=univ) (fun i _=> summable_sum (s:=univ) fun j _=> hg i j)]
  exact tsum_congr fun b=> (soaking f M o x b (hp b)).symm

section p
variable {G : Gauge} {j : ℕ}{v : Train j} {k₀ : ℝ}
-- real, full G TAKE n-period rolled into all copy weights (unbounded support, not strip)
def plaza (G : Gauge) (k : ℝ) (v : Train j) (p:Option Side) : Row (Loc G 1) (Loc G 1) :=
    colored G (fun i j z=> p.elim (olog k v i j z) (fun c=> bedtime k v c (0,i) (wrap c z,j)))
lemma plaza_m (o : Site c) (b : Beads (Loc G 1) (r+2)): tuneS (plaza G k₀ v (some c)) none b = tensor G (bedtime k₀ v c) (silks o b 0) (silks o b (Fin.succ (0:Fin _))) := by
  let i:=b 0; let j:=b (Fin.succ (0:Fin _)); change plaza G k₀ v (some c) i.2 j.2 (j.1-i.1) = tensor G _ (o+wrap c i.1,i.2) (o+wrap c j.1,j.2); unfold plaza YM.RG08.colored tensor; simp only [of_apply]; split
  · rw [trace_nimb v _ (o+wrap c i.1)]; simp [Option.elim]
  rfl
lemma portion (G:Gauge)(hp : 0 < k₀) (hj : 4 ≤ j) : ∃ c : ℝ, 0 ≤ c ∧ ∀ v:Train j, Plaque (plaza G k₀ v none) c ∧ ∀ n: Side,Even n.val→ Plaque (plaza G k₀ v (some n)) c := by
    obtain ⟨c,hc,H⟩:= poet_kern hp hj
    refine ⟨c,hc,fun v=> ⟨⟨hc,fun i j x=>?_⟩,fun n hn=>⟨hc,fun i j x=>?_⟩⟩⟩
    · unfold plaza YM.RG08.colored; split; exact (H v _ _ _).1; rwa [norm_zero]
    unfold plaza YM.RG08.colored; split; exact (H v _ _ _).2 n hn; rwa [norm_zero]
lemma dormer (G:Gauge)(hp:0<k₀)(hj:4 ≤ j)(v : Train j) (n:ℕ→Side) (ht:Tendsto (fun i=>(n i).val) atTop atTop)(hv:∀ i,Even (n i).val): Tendsto (fun i=> plaza G k₀ v (some (n i))) atTop (𝓝 (plaza G k₀ v none)) := by
    apply tendsto_pi_nhds.mpr; intro a; apply tendsto_pi_nhds.mpr; intro b; apply tendsto_pi_nhds.mpr; intro z
    unfold plaza YM.RG08.colored; split_ifs with h
    · exact poet_ends hp hj _ _ _ z _ ht hv
    exact tendsto_const_nhds
end p
-- passive marks
omit [DecidableEq α] [Fintype α] in
def fig (K : Row α α)(U:Spine E α)(n r : ℕ): Quire.Rooted E α r := match n with
  | 0 => U r
  | n+1 => ((↑(n+1:ℕ)):ℝ)⁻¹ • jib none K (fig K U n (r+2))
omit [DecidableEq α] [Fintype α] in
def frisk (K : Row α α)(U : Spine E α)(L r : ℕ) : Quire.Rooted E α r := ∑ i∈range (L+1),fig K U i r
omit [DecidableEq α] [Fintype α] in
lemma song_front (H : Plaque K A)(he : ∀ i,Tidy (U i))(n r) : Tidy (fig K U n r) := by
  induction n generalizing r with
  | zero=> rw [fig]; exact he _
  | succ i ih=> rw [fig]; exact Tidy.scale (disciples _ (ih _|>.pens) H) _
omit [DecidableEq α] [Fintype α] in
lemma pol_front (H : Plaque K A)(h:∀ i,Polished (U i))(n r): Polished (fig K U n r):= by
  induction n generalizing r with
  | zero=> rw [fig]; exact h r
  | succ i ih=>rw [fig]; exact polished_scale (fil_pol (ih _) H) _
omit [DecidableEq α] [Fintype α] in
lemma fare_front (H:Plaque K A){B:ℝ}{P: ℕ→ Row α α}{Q:ℕ→Spine E α}(hp:Tendsto P atTop (𝓝 K))(hB: ∀ i, Plaque (P i) B)(ht:∀ i,Hurled (fun x=>Q x i) (U i))(n r):
    Hurled (fun i=>fig (P i) (Q i) n r) (fig K U n r):= by
  induction n generalizing r with
  | zero=> simp_rw [fig]; exact ht _
  | succ i ih=>simp_rw [fig]; exact (fills_cut hp hB H (ih _)).scale _
omit [DecidableEq α] [Fintype α] in
lemma fare_walk (H:Plaque K A){B:ℝ}{P: ℕ→ Row α α}{Q:ℕ→Spine E α}(hp:Tendsto P atTop (𝓝 K))(hB: ∀ i,Plaque (P i) B)(ht:∀ i,Hurled (fun x=>Q x i) (U i))(n r):
    Hurled (fun i=>frisk (P i) (Q i) n r) (frisk K U n r):= Hurled.additions _ (fun j _=> fare_front H hp hB ht j r)
lemma fig_earned (M:Matrix (Co c α) (Co c α) ℝ) (o:Site c) (H : Plaque K A)
    (hh : ∀ n (b:Beads α (n+2)), tuneS K none b=M (silks o b 0) (silks o b (Fin.succ (0:Fin _))))
    (he : ∀ i,Tidy (U i))(g:E→L[ℝ] ℝ) (n r): stitch (g ∘ fig K U n r) c o=terraces M (fun r=> stitch (g∘ U r) c o) n r:= by
  induction n generalizing r with
  | zero=> simp_rw [fig,terraces]
  | succ i ih=>
    let F:= fig K U i (r+2); have hz : Tidy F:=song_front H he ..
    have hV:= (disciples _ hz.pens H).pens.shaped g
    rw [fig,show g ∘ (((↑(i+1:ℕ)):ℝ)⁻¹ • jib none K F)= ((↑(i+1:ℕ)):ℝ)⁻¹ • (g ∘ jib none K F) from funext fun _=> map_smul ..,st_scale _ hV.of_norm,phil_echo hz.pens H g,fil_knots (Tidy.map _ hz) H o M (hh _),show F=_ from rfl, show stitch (g ∘ F) _ o= _ from ih _,terraces]
lemma earns (M:Matrix (Co c α) (Co c α) ℝ)(o:Site c)(H: Plaque K A)
    (hh : ∀ n (b:Beads α (n+2)), tuneS K none b=M (silks o b 0) (silks o b (Fin.succ (0:Fin _))))
    (he : ∀ i,Tidy (U i))(g:E→L[ℝ] ℝ) (n r): stitch (g∘frisk K U n r) c o=harvestL M (fun r=> stitch (g∘U r) c o) n r:= by
    unfold frisk harvestL; rw [graft, st_sums _ (fun i _=> ((song_front H he i _).pens.shaped g).of_norm)]
    exact sum_congr rfl fun i _=> fig_earned M o H hh he g i r
end YM.RG08.Pivot
