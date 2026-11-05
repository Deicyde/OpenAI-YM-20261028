import YM.RG08.Spin.Neat
/-! # Wick-kernel orientation commutes through point transfer. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.RG08.Spin
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Source Source.Drops Labels Summit Scores Door Run Pill Matrix PowerSeries Pivot Carrier Place Scores.Pages Drift
open scoped BigOperators Topology Real ContDiff
open Wings Summit
variable {G:Gauge}{c f : Side}{E e r d τ D j t n k m l :ℕ}{R C:ℝ}{F:Labels.Frame G d}{s:Signed}{h:1/2≤R}{Z : Ratio c f}{X Y: Spine (Voice D R) (Loc G 1)}
-- use board wrappers to tile. h honors rank.
lemma peak_spin (hp:0<C)(H :4 ≤ j)(v:Train j)(m:Side)(hm:Even m.val)(hx:∀ i,Tidy (X i))(hy:∀ i,Tidy (Y i))(h : ∀ (i:Site m) (φ:Exam D) r (x:Link G m), rootSong (plug φ R∘X r) m (s.act i) x=rootSong (plug (twisting s φ) R∘ Y r) m i (orderTurn s x)) (i:Site m)(φ:Exam D)(x:Link G m):
   rootSong (plug φ R∘ frisk (plaza G C v (some m)) X n r) m (s.act i) x=rootSong (plug (twisting s φ) R ∘frisk (plaza G C v (some m)) Y n r) m i (orderTurn s x):= by
     obtain ⟨B,B0,hB⟩:= portion G hp H
     let M:= FreeResolvent.tensor G (bedtime C v m); let Q:=plaza G C v (some m); let F:=rotM s m G
     let A j:=recitalP (X j) (s.act i) φ; let D' j:= recitalP (Y j) i (twisting s φ)
     have hh (j): A j=twistV F (D' j) := by
       apply Tensor.ext_diag _ _ ((Tidy.map (plug φ R) (hx j)).sym (s.act i)) (turns_sym F ((Tidy.map _ (hy j)).sym i)); funext p
       exact (h i φ j p).trans (Eq.symm (by unfold Tensor.diagonal; rw [twists]; simp_rw [F,rot_eval]; rfl)) -- wrong parse implicit expected
     have hU: harvestL M A n r=twistV F (harvestL M D' n r):= by rw [funext hh, harvest_swap, show F*M*Fᵀ=M from rot_eq s v m G]
     unfold rootSong; rw [earns M (s.act i) ((hB v).2 m hm) (fun r b=> plaza_m (s.act i) b) hx _ n r, earns M i ((hB v).2 _ hm) (fun r b=> plaza_m ..) hy _ n r]; change Tensor.diagonal (harvestL M A n r) x=Tensor.diagonal (harvestL M D' n r) (orderTurn s x)
     rw [hU]; unfold Tensor.diagonal; rw [twists]; simp_rw [F,rot_eval]
-- moving x-tips with Hurled. Qual independent.
lemma crest_sig {U V:BoardU D R G}(hp:0<C) (hc:4 ≤ j)(w:Train j)(hX:∀ i j,Tidy (U i j))(hY:∀ i j,Tidy (V i j))(h:∀ i,Honor s U V i)(m : Side):
     let P:= plaza G C w none
     Honor s (fun i r=>frisk P (U i) n r) (fun i r=>frisk P (V i) n r) m:= by
     intro P; let c(i):=even_side i*m
     have ht: Tendsto (fun i=> (c i).val) atTop atTop:= tendsto_atTop_mono (fun i=> Nat.le_mul_of_pos_right (even_side i).val m.property) evenings_grow
     have hv i: Even (c i).val:= (evenings i).mul_right _
     let A (i:ℕ)(U:BoardU D R G)(j r:ℕ):=frisk (plaza G C w (some (c i))) (U j) n r
     obtain ⟨C,hC,HE⟩:= portion G hp hc
     have hu (U:BoardU D R G)(hU:∀ i j,Tidy (U i j))(i r:ℕ): Hurled (fun j=> A j U i r) (frisk P (U i) n r):= fare_walk (HE w|>.1) (dormer G hp hc w c ht hv) (fun i=> (HE w).2 _ (hv i)) (fun j=> Hurled.fixed (hU i j|>.pens)) n r
     have ha i: Honor s (A i U) (A i V) (c i):= by intro z φ e r x; exact peak_spin hp hc w (c i) (hv i) (hX e) (hY e) (fun i φ r x=> h _ i φ e r x) z φ x
     exact Honor.moving (hu U hX) (hu V hY) (fun i=> slant_travel (show Ratio (even_side i) (c i) from ⟨m,rfl⟩) (ha i) (fun j r=>(hu U hX j r).ever i) (fun j r=>(hu V hY j r).ever i))
end YM.RG08.Spin
