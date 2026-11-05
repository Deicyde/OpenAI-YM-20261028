import YM.Dash.Inert
import YM.Next.RANK.Bought


/-!
# Don't wait for `S` smooth when proving shortage

The early `monitor` uses all separated compact tests (not only Maxwell Gram). Point at the generic measurements of the purchases, even though k uses
shrinking scales. For each fixed k these measurements with all slots are
on the quotient by the monitor at that S. Their Maxwell limits can thus
test columns for shortage without ever measuring a test through a tie.

`EquationCount` is the needed extra finite rank input on the RBin data .
Do *not* silently assume it of any R carrying a RelayBin. For lower-cost reuse we
ask only the necessary inequality; no continuum S null-space dimensions in it.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Detect
open Function Set Filter RG Lattice Wilson Cells MeasureTheory Extraction Dash Market
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff ENNReal

variable {G : Gauge} {L : Register G}

lemma watches {S : Table L} {d : ℕ} (H : Live S) (p : Dash.old S) (a : L.Ref d) (ha : a ∈ monitor S H d) (n : ℕ)
    (v : Fin n → L.Token) (i : Fin n) (hv : v i=⟨d,a⟩) : EqOn (fun x => S.read x v) 0 (generic n) := by
  let U := generic n
  have hu : IsOpen U := genericOpen _
  let F := fun x => S.read x v
  have hh : ContinuousOn F U := p n v
  have he : ∀ᵐ x : Points n, x ∈ U → F x=0 := hu.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ:=volume)
      (hh.locallyIntegrableOn hu.measurableSet) (fun g hg ht hs => by
        let f : Points n→ℂ := Complex.ofRealCLM ∘ g
        have hx : tsupport f = tsupport g := by unfold tsupport; rw [show support f = support g by ext; simp [f]]
        let y : Test n := ⟨f, Complex.ofRealCLM.contDiff.comp hg, by rw [HasCompactSupport,hx]; exact ht,
          hx ▸ hs.trans (generic_conf n)⟩
        rw [← (Dash.notices S H a).mp ha n v i hv y]
        unfold Test.applyTo; apply integral_congr_ae; exact Eventually.of_forall fun x => Complex.real_smul)
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' hu.measurableSet).2 he) hu hh continuousOn_const

variable {C : Family G} {S : Table C.book} {d : ℕ} {f f' : Extraction.Order} {X : Columns C S d} {Z : X.Trials}

private lemma functional (i : Fin X.amount) : ∃ F : (standard C).Field d →ₗ[ℂ] ℂ,
    ∀ x, F x=(X.row i).tests (standard C) X.basis x := by
  let T := standard C
  let n := (X.row i).extra
  let p := (X.row i).expected
  let r (j : Fin n) := X.basis ((X.row i).uses j)
  let v (j : Fin n) : (Maxwell.standard C.labels).Token := ⟨d,T.representative d (r j)⟩
  let F := (T.injectFront v p d).comp (T.representative d)
  refine ⟨F,fun x => ?_⟩
  change T.read p (Fin.cons ⟨d,T.representative d x⟩ v)=T.useAt T p (Fin.cons ⟨d,x⟩ (fun i => ⟨d,r i⟩))
  let H (a : T.Tag) := (⟨a.1,T.representative a.1 a.2⟩ : (Maxwell.standard C.labels).Token)
  change _= T.read p (H ∘ (Fin.cons (α:=fun _ => T.Tag) ⟨d,x⟩ (fun i => ⟨d,r i⟩)))
  congr 1; funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl

private lemma economic (H : Live S) (c : Purchases Z) (p : Dash.old S) (k : ℕ) (i : Fin X.amount) :
    ∃ F : (C.label d ⧸ monitor S H d) →ₗ[ℂ] ℂ, ∀ j : Fin (X.dim+1), F ((monitor S H d).mkQ (Z.later k j))=S.read (Z.realPlace k i) (echoes Z k i j) := by
  let v := (fun a : Fin (X.row i).extra => (⟨d,Z.later k ((X.row i).uses a)⟩ : C.book.Token))
  let P := monitor S H d
  let F := S.injectFront v (Z.realPlace k i) d
  have he : P ≤ LinearMap.ker F := by
    intro x hx
    let y := Fin.cons (α:=fun _ : Fin ((X.row i).extra+1) => C.book.Token) ⟨d,x⟩ v
    exact watches H p x hx _ y 0 (by simp [y]) (c.axis k i)
  refine ⟨P.liftQ F he,fun a => ?_⟩
  change S.read _ _ = S.read (Z.realPlace k i) (echoes Z k i a)
  -- first argument projection at a, rest fixed
  congr 1; funext j; refine Fin.cases ?_ (fun _ => ?_) j <;> rfl

lemma measured (H : Live S) (w : Dash.old S) (h : Purchases Z) (hp : C.Makes) (hx : lands Z f) (he : f.PointLimits C S) :
    ∀ᶠ k in atTop, LinearIndependent ℂ (fun i => (monitor S H d).mkQ (Z.later k i)) := by
  choose J hJ using fun i : Fin X.amount => functional (X:=X) i
  choose U hu using fun k i => economic H h w k i
  let A := LinearMap.pi J
  let B k := LinearMap.pi (U k)
  have hf : Injective A := by
    intro x y H; apply X.full
    funext i; dsimp only; simp_rw [← hJ]; exact congr_fun H i
  have ht : LinearIndependent ℂ (fun i => A (X.basis i)) := X.basis.linearIndependent.map' A (LinearMap.ker_eq_bot.mpr hf)
  let F := fun k i => B k ((monitor S H d).mkQ (Z.later k i))
  have hv : Tendsto F atTop (𝓝 (fun i => A (X.basis i))) := by
    apply tendsto_pi_nhds.mpr; intro i
    apply tendsto_pi_nhds.mpr; intro j
    change Tendsto (fun k => U k j ((monitor S H d).mkQ (Z.later k i))) atTop (𝓝 (J j (X.basis i)))
    simp_rw [hu,hJ]; exact h.converge hp hx he j i
  filter_upwards [hv.eventually ht.eventually] with k hk; exact LinearIndependent.of_comp (B k) hk

/-- Upper-equation finite budget associated with the Bin.
It's enough to have it at frequently many `(N,p)` in this extraction (full
reconstruction path expects actual all-p certificates). -/
def EquationCount (x : Bin S) (f : Extraction.Order) (d : ℕ) := ∃ᶠ i in f.fuse,
    Module.finrank ℂ (C.label d) ≤ Module.finrank ℂ (LinearMap.ker ((x d).step i).toLinearMap) +
      Module.finrank ℂ ((standard C).Field d)

private lemma ker_compare {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (A B : V →L[ℂ] V) (h : ‖A-B‖ < 1) (hp : ∀ x : V, B (B x)=B x) :
    Module.finrank ℂ (LinearMap.ker A.toLinearMap) ≤ Module.finrank ℂ (LinearMap.ker B.toLinearMap) := by
  let F : LinearMap.ker A.toLinearMap →ₗ[ℂ] V := (LinearMap.id-B.toLinearMap).comp (LinearMap.ker A.toLinearMap).subtype
  have he (x : LinearMap.ker A.toLinearMap) : F x ∈ LinearMap.ker B.toLinearMap := by
    change B (x.val-B x.val)=0
    rw [map_sub,hp,sub_self]
  let g := LinearMap.codRestrict (LinearMap.ker B.toLinearMap) F he
  apply LinearMap.finrank_le_finrank_of_injective (f:=g)
  rw [← LinearMap.ker_eq_bot]; apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  have hr : B x.val=x.val := Eq.symm (sub_eq_zero.mp (congr_arg Subtype.val hx))
  have hv : (A-B) x.val= -x.val := by rw [sub_apply, hr,show A x.val=0 from x.property, zero_sub]
  have hu := (A-B).le_opNorm x.val; rw [hv,norm_neg] at hu
  apply Subtype.ext; by_contra hh
  have hg := norm_pos_iff.mpr (show x.val ≠ 0 from hh)
  linarith [mul_lt_mul_of_pos_right h hg]

lemma reconciled (x : Bin S) (h : Bin.Matrix x d f) : ∀ᶠ i in f.fuse,
    Module.finrank ℂ (LinearMap.ker ((x d).step i).toLinearMap)=Module.finrank ℂ (LinearMap.ker (x d).trueP.toLinearMap) := by
  let A := x d
  filter_upwards [h.eventually (Metric.ball_mem_nhds _ zero_lt_one)] with i hi
  have he : ‖A.step i-A.trueP‖ < 1 := by rw [← dist_eq_norm]; exact hi
  exact le_antisymm (ker_compare _ _ he A.final) (ker_compare A.trueP _ (by rw [norm_sub_rev]; exact he) (A.projection i))

lemma demanded (h : Live S) (w : Dash.old S) (p : Purchases Z) (hp : C.Makes) (hx : lands Z f') (he : f'.PointLimits C S) (x : Bin S) (hm : Bin.Matrix x d f)
    (hd : EquationCount x f d) : Bin.shortage x h d := by
  obtain ⟨i,hi,hb⟩ := (hd.and_eventually (reconciled x hm)).exists
  obtain ⟨k,hk⟩ := (measured h w p hp hx he).exists
  have H := hk.fintype_card_le_finrank
  have hv := (monitor S h d).finrank_quotient_add_finrank
  change Module.finrank ℂ (C.label d ⧸ monitor S h d)+Module.finrank ℂ (monitor S h d)=Module.finrank ℂ (C.label d) at hv
  change Fintype.card _ ≤ Module.finrank ℂ (C.label d ⧸ monitor S h d) at H
  rw [hb,Module.finrank_eq_card_basis X.basis] at hi
  unfold Bin.shortage
  omega

/-- Once equations are propagated, proves full field count on the monitored quotient. -/
theorem stocked (h : Live S) (w : Dash.old S) (p : Purchases Z) (hp : C.Makes) (hx : lands Z f') (he : f'.PointLimits C S)
    (x : Bin S) (hm : Bin.Upper x f d) (Ho : f.Ordered C S) (hd : EquationCount x f d) :
    (monitor S h d)=LinearMap.ker (x d).trueP.toLinearMap ∧
    Module.finrank ℂ (C.label d ⧸ monitor S h d)=Module.finrank ℂ ((standard C).Field d) ∧
      ∀ᶠ k in atTop, Submodule.span ℂ (Set.range fun i => (monitor S h d).mkQ (Z.later k i))=⊤ := by
  have hy := demanded h w p hp hx he x hm.slides hd
  have hT : monitor S h d=LinearMap.ker (x d).trueP.toLinearMap := Eq.symm (Bin.exactC x Ho hm hy)
  have hab := measured h w p hp hx he
  have hv : Fintype.card (Fin (X.dim+1))=Module.finrank ℂ (C.label d ⧸ monitor S h d) := by
    obtain ⟨k,hk⟩ := hab.exists
    apply le_antisymm hk.fintype_card_le_finrank
    obtain ⟨j,hg,hc⟩ := (hd.and_eventually (reconciled x hm.slides)).exists
    rw [hc,← hT,Module.finrank_eq_card_basis X.basis] at hg
    have hi : Module.finrank ℂ (C.label d ⧸ monitor S h d)+Module.finrank ℂ (monitor S h d)=Module.finrank ℂ (C.label d) := (monitor S h d).finrank_quotient_add_finrank
    change Module.finrank ℂ (C.label d ⧸ monitor S h d) ≤ _
    omega
  exact ⟨hT,hv.symm.trans (Module.finrank_eq_card_basis X.basis).symm,hab.mono fun _ h => LinearIndependent.span_eq_top_of_card_eq_finrank h hv⟩
end YM.Next.Rank.Detect
