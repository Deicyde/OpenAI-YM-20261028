import YM.TraceExtension.Prom.Zoom.Boats
set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Filter Function Set MeasureTheory Analysis Extraction Table Ward Climb
open scoped Topology FourierTransform ContDiff BigOperators
variable {n : ℕ}

open MergeProof.East
variable {G:Gauge}{C:Family G}{S:Table C.book}{F:Extraction.Order} {D:ℕ}
lemma harvestedSky (H : S.Hierarchy) (h : F.Ordered C S) (a : (Bel C.book).RealSpin)
    (X : Station C D) {N : ℕ} {R ε : ℝ} (hs : X.Admissible F a N R ε) (𝓛:Ultrafilter (ℕ × ℕ))(hℓ:(𝓛:Filter _) ≤ F.fuse)
    (hu : ∀ d:Fin (D+1),∀ᶠ j:ℕ × ℕ in F.fuse,X.atCut j d ((Bel C.book).unit d)=C.book.scalar d) :
    ∃ U : Panel S, ∃ Y : Lifts C D,Tendsto X.atCut (𝓛:Filter _) (𝓝 Y) ∧ (∀ d : Fin (D+1),∀ x,U d x=S.project d (Y d x))∧
      (∀ d≤D, StraightAt H.spin a U d) ∧ (∀ d≤D,U d ((Bel C.book).unit d)=S.unit d) ∧
      ∀ (n : ℕ), n ≤ N → ∀ v : Fin n → (Bel C.book).Tag, (∀ i,(v i).1 ≤ D) →
        ∀ t : Test n, tsupport t ⊆ Scaling.window R n →
        ∀ M : ℝ, 0 < M → (∀ x, ‖t x‖ ≤ M) →
        ‖t.applyTo (tested X.r U v) - t.applyTo (disc v)‖ ≤ ε * Station.charge v * M := by
  obtain ⟨A,hA⟩ := hs.lift_bound
  obtain ⟨b,hb,hU,Y,hY⟩ := finite_extract (𝓛:=(𝓛:Filter _)) X.atCut A ((show ∀ᶠ i : ℕ×ℕ in F.fuse, ‖X.atCut i‖ ≤ A from hA).filter_mono hℓ)
  have hς:=𝓛.unique hb
  have hb := hb.trans hℓ
  have he i (x) : Tendsto (fun j => X.atCut j i x) b (𝓝 (Y i x)) :=
    Dash.arcing (tendsto_pi_nhds.mp hY i) tendsto_const_nhds
  let U (d : ℕ) : (Bel C.book).Field d →ₗ[ℂ] S.Field d :=
    if h : d≤D then (S.project d).comp (Y (⟨d,Nat.lt_succ_of_le h⟩ : Fin (D+1))).toLinearMap else 0
  have eq (d : ℕ) (h : d≤D) x : U d x=S.project d (Y ⟨d,Nat.lt_succ_of_le h⟩ x) := by simp only [U,dif_pos h]; rfl
  let z : Fin (D+1) := ⟨0,Nat.succ_pos _⟩
  refine ⟨U,Y,hς ▸ hY,(fun d=> eq d (Nat.le_of_lt_succ d.isLt)),fun d hd => ?_, ?_, fun n hn v hv t ht M hm ht' => ?_⟩
  · let i : Fin (D+1) := ⟨d,Nat.lt_succ_of_le hd⟩
    constructor
    · intro x; rw [eq d hd,eq d hd,S.conj_project]; apply congr_arg
      exact tendsto_nhds_unique_of_eventuallyEq (he i ((Bel C.book).conj a d x)) (he i x).star
        (((show ∀ᶠ j in F.fuse, ∀ (i : Fin (D+1)) v, X.atCut j i ((Bel C.book).conj a i v) = star (X.atCut j i v) from hs.lift_real)).filter_mono hb |>.mono fun _ h => h i x)
    intro s x; rw [eq d hd,eq d hd,S.mirror_project]; apply congr_arg
    exact tendsto_nhds_unique_of_eventuallyEq (he i ((Bel C.book).mirror a d s x))
      ((C.book.mirrorGroup d s).continuous_of_finiteDimensional.continuousAt.tendsto.comp (he i x))
      (((show ∀ᶠ j in F.fuse, ∀ (i : Fin (D+1)) s v, X.atCut j i ((Bel C.book).mirror a i s v) = C.book.mirrorGroup i s (X.atCut j i v) from hs.lift_signed)).filter_mono hb |>.mono fun _ h => h i s x)
  · intro d hd; rw [eq d hd];apply congr_arg (S.project d)
    exact tendsto_nhds_unique_of_eventuallyEq (he ⟨d,Nat.lt_succ_of_le hd⟩ ((Bel C.book).unit d)) tendsto_const_nhds ((hu _).filter_mono hb)
  let g : Caps n := fun i => (v i).1
  let m (j) (i : Fin n) : C.book.Ref (g i) := X.atCut j ⟨g i,Nat.lt_succ_of_le (hv i)⟩ (v i).2
  let y (i : Fin n) : C.book.Ref (g i) := Y ⟨g i,Nat.lt_succ_of_le (hv i)⟩ (v i).2
  have hh : S.integralOn g y (dilate X.rad t)=t.applyTo (tested X.r U v) := by
    unfold Table.integralOn; rw [zoom_integral]
    apply t.apply_eq; intro x hx
    change S.value g _ y = S.useAt S _ (panels U ∘ v)
    let l : Fin n → C.book.Token := fun i => ⟨g i,y i⟩
    rw [show panels U ∘ v = S.classTokens ∘ l from funext (fun i => by
      unfold panels Function.comp
      change Sigma.mk (g i) (U (g i) ((v i).2)) = Sigma.mk (g i) (S.project (g i) (y i))
      rw [eq _ (hv i)])]
    exact (S.at_project S H.laws.toSymmetric (fun _ => le_rfl) ((enlarged X.rad _).1 hx) l).symm
  have hz : Tendsto (fun j : ℕ×ℕ => X.paid v hv t j.1 j.2) b (𝓝 (t.applyTo (tested X.r U v))) := hh ▸
    calibrated_smear h b hb _ (v:=m) (x:=y) fun i => he ⟨(v i).1,Nat.lt_succ_of_le (hv i)⟩ (v i).2
  refine le_of_forall_pos_le_add fun η hη => ?_
  exact le_of_tendsto ((hz.sub_const (t.applyTo (disc v))).norm)
    ((show ∀ᶠ i in F.fuse, ‖X.paid v hv t i.1 i.2 - t.applyTo (disc v)‖ ≤ ε * Station.charge v * M + η from
      hs.short hn v hv t ht M hm ht' η hη).filter_mono hb)
end YM.Next.UVStress
