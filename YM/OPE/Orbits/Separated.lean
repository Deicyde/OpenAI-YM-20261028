import YM.OPE.Orbits.System

/-! Single cluster endpoint: fixed real/covariant prescription, ground algebra
and all viewer error, quantitative separated powers at *every finite horizon*.
Outer clearance may also be power-separated for later reuse. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Orbits
open Function Set Filter MeasureTheory Table Extraction Reader
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{S:Table C.book}{F:Order}
    (U:Spec.Final C F S) (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
    (h:Services C F S){I J K:Type}[Fintype I][Fintype J] {d:I→ℕ}{e:J→ℕ} (v:Labels S d)(w:Labels S e)
    {A:K→ℝ}{φ:Filter K}{a b c:ℝ}{x:K→I→E4}{y:K→J→E4}{o:K→E4}(hA:Tendsto A φ atTop)[φ.NeBot]
    (hx:enveloped φ A a x o)(hk:Kept φ A a x)(ha:0 < a)
include h hA hx hk ha
lemma coefficient_rate (m:ℕ)(j:R.channels m): RateLE φ A (fun i=>R.coef m j (x i) v (o i)) ((weight d-m)*a):=by
    let V i: R.stratum m:=⟨R.fresh m (x i) (o i) v,R.fresh_mem _ _ _ _⟩
    let f: R.stratum m →ₗ[ℝ] ℂ:= ((R.basis m).coord j).restrictScalars ℝ
    have hM : RateLE φ A V ((weight d-m)*a):= (fresh_price (o:=o) U R h hA v hx hk ha m).transfer (Eventually.of_forall (fun i=> le_refl _))
    letI:FiniteDimensional ℝ (R.stratum m):= Module.Finite.trans ℂ _
    exact pay_fixed (x:=V) hA f hM

variable (hp:Intervals φ A b (fun l=>sole (o l)) y)(hy:Kept φ A c y)(hb:0≤ b)(hc:b≤c)(hba:b < a)

include hp hy hba hb hc in
lemma all_rate (t:K→Viewers U)(D:ℕ):RateLE φ A (fun i=>formula U R (x i) (o i) v (y i) w D (t i)) (weight d*a - (D+1:ℝ)*(a-b)+weight e*c):=by
   apply RateLE.congr (balance_rate U R h hA v hx hk ha t w hp hy hb hc D hba) (Eventually.of_forall fun i=>tested_fields ..)
include hp hy hb hc hba
lemma algebra_rate (m:ℕ): RateLE φ A (fun i=> algebraError U R (x i) (o i) v (y i) w m) (weight d*a-(m+1:ℝ)*(a-b)+weight e*c):=by
   obtain ⟨h₁,h₂⟩:= clearance_both hA hx hk hp hy hba hc
   let f(k:K)(v':Viewers U):= balance U (spectator U v') R m (x k) (o k) v (y k) w
   have ht(v'):= balance_rate U R h hA v hx hk ha v' w hp hy hb hc m hba
   intro s hs; filter_upwards [universalize (p:=fun k v'=> ‖f k v'‖ ≤ Real.exp (s*A k)) (fun v'=> ht v' s hs), h₂,h₁] with i he hi ho
   exact (glance_contract U (Real.exp_nonneg _)).2 (fun t => by rw [see_algebra]; exacts [he t, hi, ho])

-- finite radius-tail demands. All positions and exteriors chosen after the threshold.
variable {r:K→ℝ}{M η δ ε:ℝ}(hM:0≤ M)(hη:0<η)(hε:0<ε)(hr:Tendsto r φ (𝓝[>] 0))
   (hx':∀ᶠ i in φ,WithinRoom (r i) M η (x i) (o i))(hy':∀ᶠ i in φ,ClearOf (o i) (y i) δ)
omit hA hx ha hk hp hy hb hc hba
include h hM hη hε hr hx' hy'
omit hy' in
private lemma channel_prelim (m:ℕ)(j:R.channels m):∀ᶠ i in φ,‖R.coef m j (x i) v (o i)‖≤ (r i)^((m:ℝ)-weight d-ε):=by
   obtain ⟨hx,hk⟩:=room_regime hr hM hη hx'; have hT:=run_towards hr; have h':=coefficient_rate U R h v hT hx hk (zero_lt_one) m j
   exact ((loglife hr).rpow ((m:ℝ)-weight d-ε)).outweigh h' (by linarith only [hε]) hT
private lemma exterior_prelim (D:ℕ)(hδ:0<δ):∀ᶠ i in φ,‖algebraError U R (x i) (o i) v (y i) w D‖≤ (r i)^((D:ℝ)+1-weight d-ε):= by
   obtain ⟨hx,hk⟩:=room_regime hr hM hη hx'; let T:=run ∘ r; have Tt: Tendsto T φ atTop := run_towards hr
   obtain ⟨hc,hp⟩:=free_clear Tt hδ hy'; have hQ:=algebra_rate U R h v w Tt hx hk zero_lt_one hp hc le_rfl le_rfl zero_lt_one D
   refine ((loglife hr).rpow ((D:ℝ)+1-weight d-ε)).outweigh hQ ?_ Tt; linarith only [hε]
omit hr hx' hy'
include hM hη hε

omit hε h in
lemma admissible_separated (D:ℕ): ∀ᶠ r:ℝ in 𝓝[>] 0,∀ x:I→E4,∀o:E4, WithinRoom r M η x o→∀ n ≤ D,orbitMargin R.port n x o:=by
    let P(u:ℝ)(z:(I→E4)× E4):=WithinRoom u M η z.1 z.2
    haveI:(nhdsWithin (0:ℝ) (Set.Ioi 0)).NeBot:=inferInstance
    have h'':∀ᶠ u:ℝ in 𝓝[>] 0,∀ z:(I→E4)× E4,P u z→ orbitMargin R.port D z.1 z.2 := by
          apply refine_geometry; intro f ψ hψ hw hh
          obtain ⟨hx,hk⟩:=room_regime (r:=id) (φ:=ψ) (X:=fun i=>(f i).1) (O:=fun i=>(f i).2) (show Tendsto id ψ (𝓝[>] 0) from tendsto_id.mono_left hw) hM hη hh
          exact ⟨_,hψ,le_rfl, margins U R (run_towards (r:=id) (φ:=ψ) (tendsto_id.mono_left hw)) hx hk zero_lt_one D⟩
    filter_upwards [h''] with s hs x y hx m hm
    exact fun i hi=> hs (x,y) hx i ((full_bands ..).mpr (((full_bands ..).mp hi).trans hm))

lemma coefficient_separated (m:ℕ)(j:R.channels m): ∀ᶠ r:ℝ in 𝓝[>] 0,∀ (x':I→ E4)(o':E4), WithinRoom r M η x' o' → ‖R.coef m j x' v o'‖ ≤ r^((m:ℝ)-weight d-ε) := by
   let P r (u:(I→ E4)× E4):= WithinRoom r M η u.1 u.2
   let Q (r:ℝ)(u:(I→E4)× E4):=‖R.coef m j u.1 v u.2‖ ≤ r^((m:ℝ)-weight d-ε)
   have hf:∀ᶠ t in 𝓝[>] (0:ℝ),∀ y:(I→E4)× E4, P t y→Q t y:=by
       refine refine_geometry (P:=P) (Q:=Q) fun f ψ hψ hl hh=>?_ ; exact ⟨_,hψ,le_rfl,channel_prelim (r:=id) (K:=ℝ) (x:=fun s=>(f s).1) (o:=fun s=>(f s).2) U R h v hM hη hε (tendsto_id.mono_left hl) hh m j⟩
   filter_upwards [hf] with t ht x' o' h using (ht ⟨x',o'⟩ h)
include h
lemma quantitative_separated (D:ℕ)(hδ:0<δ) :∀ᶠ r:ℝ in 𝓝[>] 0,∀ (x:I→E4)(o:E4)(y:J→E4), WithinRoom r M η x o → ClearOf o y δ →
   Injective (beside x y) ∧ Injective (beside (sole o) y) ∧
      ‖algebraError U R x o v y w D‖≤ r^((D:ℝ)+1 - weight d-ε) ∧ ∀ t:Viewers U,‖formula U R x o v y w D t‖≤ r^((D:ℝ)+1-weight d-ε):=by
    let P (r:ℝ) (z:(I→E4) × E4 × (J→E4)):= WithinRoom r M η z.1 z.2.1 ∧ ClearOf z.2.1 z.2.2 δ
    let Q (r:ℝ)(z:(I→E4) × E4 × (J→E4)) := Injective (beside z.1 z.2.2) ∧ Injective (beside (sole z.2.1) z.2.2) ∧ ‖algebraError U R z.1 z.2.1 v z.2.2 w D‖ ≤ r^((D:ℝ)+1 - weight d-ε)
    have hf:∀ᶠ r in 𝓝[>] (0:ℝ),∀ z,P r z→ Q r z:=by
       refine refine_geometry fun f ψ hψ hl hh => ⟨_,hψ,le_rfl,?_⟩
       let x(r:ℝ):= (f r).1; let o(r:ℝ):=(f r).2.1; let y(r:ℝ):=(f r).2.2
       obtain ⟨hx,hk⟩:= room_regime (r:= id) (O:=o) (X:=x) (show Tendsto id ψ (𝓝[>]0) from tendsto_id.mono_left hl) hM hη (hh.mono fun _ hi=>hi.1)
       have hT:=run_towards (φ:=ψ) (r:=id) (tendsto_id.mono_left hl)
       obtain ⟨hq,hj⟩:= free_clear (Y:=y) (O:=o) hT hδ (hh.mono fun _ hi=>hi.2)
       exact (clearance_both hT hx hk hj hq zero_lt_one le_rfl).2.and ((clearance_both hT hx hk hj hq zero_lt_one le_rfl).1.and (exterior_prelim (x:=x) (o:=o) (y:=y) (r:=id) U R h v w hM hη hε (tendsto_id.mono_left hl) (hh.mono fun i=>And.left) (hh.mono fun i=>And.right) D hδ))
    filter_upwards [hf] with r hr x o y hx hy
    obtain ⟨h₁,h₂,hc⟩:= hr (x,o,y) ⟨hx,hy⟩
    exact ⟨h₁,h₂,hc, fun v'=> ((glance_contract U (by linarith only [hc,norm_nonneg (algebraError U R x o v y w D)])).1 hc v' |>.trans' ((congr_arg norm (formula_seen U R x o v y w D v' h₁ h₂)).symm.le))⟩
end YM.OPE.Orbits
