import YM.RG08.Curl.River
/-! # Fixed path lift addition. Readable on true arcs. Null path moments in
construction's own path and first-leg orientation. -/
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Virtue
open Filter MeasureTheory Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent FreeResolvent Profiles Finset Next.Free Conductor UVExt.Paths Push.AbsoluteSums Staffer
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {m : Side} {A B C σ η : ℝ} {r s d n : ℕ}
variable {F : Atlas G} {i : G.ColorIndex}
private lemma compose_views {X Y : Skin G (d+1)}(h : Mar X A σ)(hh:Mar Y B σ)(hp:0<σ): turnSeries (Stationary.issue (X+Y)) (m:=m) = turnSeries (Stationary.issue X) + turnSeries (Stationary.issue Y) := by
  let T:=Stationary.issue (G:=G) (t:=d+1)
  have he (x:Config G m) y n: (T (X+Y) n).unmasked x y=(T X n).unmasked x y +(T Y n).unmasked x y := by
    unfold Atom.unmasked Atom.poly -- poly in def?
    rw [← sum_add_distrib]; exact sum_congr rfl (fun _ _=> add_mul ..)
  funext v
  have hM {X:Skin G (d+1)} {A:ℝ}(h: Mar X A σ)(U:Config G m)(x): Summable (fun i=> (T X i).unmasked U x):= Summable.of_norm_bounded (h.pathways.1.2.1.mul_right ((2:ℝ)^(d+2))) (fun i=> ((T X i).unmasked_bound U x).trans (mul_le_mul_of_nonneg_right ((T X i).lower_budget σ hp) (by positivity)))
  have hf (U:Config G m): uncut (T (X+Y)) U= uncut (T X) U+uncut (T Y) U:= by unfold uncut; simp_rw [he,(hM h _ _).tsum_add (hM hh _ _)]; rw [sum_add_distrib]
  unfold T at hf; simp [turnSeries,Patch.average,hf,sum_add_distrib,mul_add]
private lemma flowLength {α:Type}[Fintype α][DecidableEq α]{X Y:Shift α→ℝ}(hp:Width σ A X)(he:Width σ B Y)(h:0<σ):
    readable (X+Y) ∘ axes = (readable X ∘ axes) + (readable Y ∘ axes) := by
  funext p
  have hh {A:ℝ}{X:Shift α→ ℝ}(hp : Width σ A X): Summable (fun i=>mode (axes p) i * (X i:ℂ)) := by
    apply Summable.of_norm; simpa only [norm_mul,mode_real _ _ (axes_real p),one_mul,Complex.norm_real] using! (hp.summable h.le).norm -- approach?
  simp only [readable,Laurent.read,Function.comp_apply,Pi.add_apply, Complex.ofReal_add, smul_eq_mul,mul_add]; exact (hh hp).tsum_add (hh he)
lemma exalts.plus {X Y : Flotilla G}{k : Finset ℕ}(h : exalts X k σ A)(hp:exalts Y k σ B)(he:0 < σ) : exalts (X+Y) k σ (A+B) ∧ ∀ m:Side,shores (X+Y) k m=shores X k m+shores Y k m := by
    refine ⟨fun i hi=>(h _ hi).plus (hp _ hi), fun m=>?_⟩
    unfold shores; rw [← sum_add_distrib]; exact sum_congr rfl (fun i hi=> compose_views (h _ hi) (hp _ hi) he)
lemma Artefact.ride {X Y : Flotilla G}{U V : Panel G}(h : Artefact U d σ A X)(hp: Artefact V d σ B Y)(he: 0 < σ)(hU:∀i ≤ d+2,Tunable (U i))(hV : ∀ i≤ d+2, Tunable (V i)) : Artefact (U+V) d σ (A+B) (X+Y):= by
    obtain ⟨hx,H⟩:= exalts.plus h.lanes hp.lanes he
    have hm : 0∈embark 0 (d+1) := by simp [embark]
    refine ⟨hx,fun i j=> ?_,fun m i hi=>?_⟩
    · change Rays 2 (readable (X 0 i j+Y 0 i j) ∘ axes); rw [show _ ∘ axes=(readable (X 0 i j) ∘ axes)+(readable (Y 0 i j)∘ axes) from flowLength ((h.lanes 0 hm).pass i j) ((hp.lanes 0 hm).pass i j) he]; exact (h.march i j).add (hp.march i j)
    rw [H m,Tensor.coeff_add ((portside h.lanes he _).analytic.contDiffAt.of_le le_top) ((portside hp.lanes he _).analytic.contDiffAt.of_le le_top), h.value _ _ hi,hp.value _ _ hi,Pi.add_apply (f:=U),recital_add (hU i hi).1 (hV i hi).1]

-- link to existing uses, both first moments (on pulled aggregation unmarked)
theorem docks {X : Flotilla G}{F : Panel G}(h : Artefact F d σ B X)(hp:0<σ) (R:PathData G)(hx:R.loop=Stationary.issue (X 0)) : ∀ i x, HasSum (R.loop_coeff i x) 0 ∧ ∀ l : Axis, HasSum (fun k => R.loop_coeff i x k *
      (((((Stationary.issue (X 0) k).leg 1).offset l - ((Stationary.issue (X 0) k).leg 0).offset l : ℤ) : ℝ))) 0 := issue_normal (h.lanes 0 (by simp [embark])).pass hp h.march R hx
end YM.RG08.Virtue
