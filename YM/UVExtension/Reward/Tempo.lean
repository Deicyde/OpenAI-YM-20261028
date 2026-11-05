import YM.UVExtension.Reward.Matches
import YM.UVExtension.Projection.Lines

/-! Graph graph query at stage. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Reward
open Lattice RG Supply Stationary Projection Precision Bloch Laurent Exterior Wilson Tree Filter Function Finset MenuView
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {s : Sheet G} {L : Rolls s} {Θ : Protection L} {a : Levels G}
    {P : MapPrices} {K V : Horizon a} {Z : ChartRatio G} {W : Delays Θ} {y : Bar W} {w : Wait y} {Q : PostCost L} {D : Knobs a} {ε : ℝ} {m N :ℕ}

-- scale for user inputs x; require normalized; segment interior etc
structure Tried (V:Horizon a) (D:Knobs a)(Q:PostCost L)(Z:ChartRatio G)(ε:ℝ)(m N:ℕ)(x y:Cube G)(b:ℝ)(z:GainWire a m):Prop where
    time : m<N
    origin : SatPath V N (m+1) (sat D V N (m+1) x)
    run : Courtesy V D Q Z ε N m (sat D V N (m+1) x) y b z
variable {I:Type}

abbrev daysF (D:Knobs a)(V:Horizon a)(x:Cube G)(N:ℕ)(z:GainWire a m):=airF D (V.H N m) (sat D V N (m+1) x) z
abbrev daysL (D:Knobs a)(V:Horizon a)(Z:ChartRatio G)(x:Cube G)(N:ℕ)(z:GainWire a m):=airL D Z (sat D V N (m+1) x) z
lemma on_peak {E X : Type}[NormedAddCommGroup E] [NormedSpace ℝ E][NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ E][FiniteDimensional ℝ X] {P: MenuView I} {f : I→ E→ℝ}{d k : ℕ}(h:Run P d k f 0)(L : X→L[ℝ] E): Run P d k (fun i=> f i ∘ L) 0:=by
  have he := (Run.fix (P:=P) L 0 k 0 L.contDiff.contDiffAt).comp (G:=f) (by simp_rw [map_zero]; exact h)
  rw [mul_zero,zero_add] at he; exact he

lemma queries [Nonempty I]{J:MenuView I}(hZ:LocalRatio Z) (t:I→ℕ)(x y:I→Cube G)(b:I→ℝ)(z:I→ GainWire a m)(h:∀ i,Tried V D Q Z ε m (t i) (x i) (y i) (b i) (z i))
    (he:∀ p,SourceBasis J (fun i=> sat D V (t i) (m+1) (x i)) (a.params (m+1)).clip (a.S.side (m+1) p) 5) (hp:∀ p, Run J 0 4 (fun i=> inputSeries (a.params m).clip (sat D V (t i) m 0) (m:=a.S.side m p)) 0):
    (∀ i j v,J.pace wavePulse fun n=> daysF D V (x n) (t n) (z n) i j v) ∧ ∀ i v,J.pace wavePulse fun n=> daysL D V Z (x n) (t n) (z n) i v:=by
  let L i : Link G (a.S.side m i) →L[ℝ] Bid.Dir G (a.S.side m i) := (arm G (a.S.side m i) 1).toContinuousLinearMap
  let F i:=treeAt a m i; let u i:=turnAt a m i
  have hx n i:= (h n).run.bubble.steps i (F i)
  have H i:= interview (F i) (u i) J (fun n=> sat D V (t n) (m+1) (x n)) (fun n=> z n i (F i)) (he i) (fun n=> (h n).origin.bound) (fun n=> (hx n i).2.1) (fun n=> (hx n i).1) (Q.price _) Z hZ
  constructor
  · intro i j v
    have hv := (on_peak (E:=Bid.Dir G (a.S.side m i)) (H i).2.1 (L i)).tests j (by have hi:=j.isLt; omega) v
    have hm:= ((hp i).more (Nat.zero_le wavePulse) le_rfl).tests j (by have hi:=j.isLt; omega) v
    exact book.mp (joins hv (acts hm (-(LinearMap.id (R:=ℝ))))) -- add_neg
  intro i v; have hv:= (on_peak (E:=Bid.Dir G (a.S.side m i)) (H i).2.2 (L i)).tests _ le_rfl v; exact book.mp hv
lemma fixed_read {J:MenuView I}(x:I→Cube G)(h : Working D V P m)(he:m ≤ N)(p k): Run J 0 k (fun i=>inputSeries (a.params m).clip (sat D V N m (x i)) (m:=a.S.side m p)) 0:=by
  have hp:=h.paid N he 0 (Submodule.zero_mem _) (by simp)
  exact Run.fix (inputSeries (a.params m).clip (sat D V N m 0) (m:=a.S.side m p)) _ _ _ (stain_knit _ _ hp.bound).analytic.contDiffAt

instance : Nonempty Team:= ⟨dash 0 0⟩
variable (t: Team→Cube G)
private lemma linear_eye {J:Type}{f: Projection.Ortho J→ℝ}(h:RLinear f) (x y: Projection.Ortho J) : (Projection.straight rower).pace 1 fun i=> f (x+rower i • y):=by
  obtain ⟨p,rfl⟩:=h
  let P:= Projection.straight rower
  simp only [map_add,map_smul]; exact P.add (P.base _ _) (P.mul (straight_axis _) (P.base 0 (p y)))
lemma sound (x y:Cube G)(X:Working D V P m)(he:m ≤ N) (v z): SourceBasis (Projection.straight rower) (fun i=> sat D V N m (x+rower i • y)) (a.params m).clip (a.S.side m v) z:=by
  let H:=label D m; let a':= fun i=>x+rower i • y
  refine ⟨fixed_read a' X he _ _,?_,?_⟩
  · refine ⟨fun i=> (H.hat_an (a' i) v).contDiffAt,fun i _ p=> book.mpr ?_⟩
    exact linear_eye (H.hat_cost i v p) x y
  refine ⟨fun i=> ?_,fun i _ p=> book.mpr (linear_eye (H.e_cost i v p) x y)⟩
  exact (turns_analytic _ (half_pos H.width_pos) (budget_hyp Sum.inl _ H.coil (a' i) (half_lt_self H.width_pos))).contDiffAt

def zeroT : Team:= ⟨0, le_rfl,zero_le_one⟩
private def oneT : Team:= ⟨1,zero_le_one, le_rfl⟩
lemma paced (b:G.ColorIndex) (hZ:LocalRatio Z) (h:Ahead wavePulse ε)(hp : Mints D P V Q Z ε){x y x' y' :Cube G} {α δ : ℝ}{ρ σ: GainWire a m}(hV:x∈ (label D (m+1)).valid)(hw:y∈(label D (m+1)).valid)(hx: ‖x‖≤ε)(hy:‖y‖≤ε)
    (he:Tried V D Q Z ε m N x x' α ρ)(he':Tried V D Q Z ε m N y y' δ σ): ‖y'-x'‖≤(1/2:ℝ)*‖y-x‖:=by
  have hh := h.small; have hε : ε≤1/4:=by linarith
  let R:= label D m; let U:=label D (m+1); let B:=hp.work m; let i := b
  have hg:=keysReady B he.time.le; have hK:=hp.work (m+1)
  rcases eq_or_ne x y with rfl|ht
  · have H : x'=y':=by
      let f: Fin 2→ℝ:= 0; let J:= Projection.straight f; let W: Fin 2→ Cube G:= ![x',y']; let z: Fin 2→ GainWire a m:= ![ρ,σ]
      let aQ: Fin 2→ℝ:=![α,δ]
      have hT n: Tried V D Q Z ε m N x (W n) (aQ n) (z n):=by
        fin_cases n; exact he; exact he'
      have HF p: SourceBasis J (fun _=> sat D V N (m+1) x) (a.params (m+1)).clip (a.S.side (m+1) p) 5:=by
        have hz: ContDiffAt ℝ ω (U.eHat x p) 0:= (turns_analytic _ he.origin.bound.width he.origin.bound.two).contDiffAt
        exact ⟨fixed_read (fun _=> x) hK he.time p 5, Run.fix _ _ _ _ (U.hat_an x p).contDiffAt, Run.fix _ _ _ _ hz⟩
      obtain ⟨h1,h2⟩:=queries hZ (fun _=> N) (fun _=> x) W aQ z hT HF (fixed_read (fun i:Fin 2=> 0) B he.time.le · 4)
      have hy {g:Fin 2→ℝ}(h:J.pace wavePulse g): g 0=g 1:=by obtain ⟨u,H,h⟩:= h; rw [h,h]; rfl
      have hc:=aligned he.run he.time B; have hr:=aligned he'.run he.time B
      rw [show airF D _ _ ρ= airF D (V.H N m) (sat D V N (m+1) x) σ from funext fun i=> funext fun j=> funext fun v=> hy (h1 i j v),
        show airL D _ _ ρ=airL D Z (sat D V N (m+1) x) σ from funext fun i=> funext fun v=> hy (h2 i v)] at hc
      exact congr_arg Prod.fst (Aligns.unicity hc hr b (organized B) hg)
    rw [H]; simp
  let d := ‖y-x‖; have hd : 0<d:= norm_pos_iff.mpr (sub_ne_zero.mpr ht.symm)
  let p := ((1/2:ℝ)/d) • (y-x); let r:= fun u=> x + rower u • p
  have hk : d ≤ 2*ε:= (norm_sub_le ..).trans (by linarith)
  let c:Team:=⟨2*d,(by positivity),(by linarith)⟩
  have hne:c≠zeroT:= by intro h; have hw:2*d=0:=congr_arg Subtype.val h; linarith
  have hz :r zeroT=x:=by change x+ (0:ℝ) • _=_; simp
  have hf : r c=y:=by
    change x+(2*d) • p=y; unfold p; rw [smul_smul,show 2*d*((1/2:ℝ)/d)=1 by field_simp,one_smul]; abel
  have hor (t:Team):SatPath V N (m+1) (sat D V N (m+1) (r t)):= hK.paid N he.time _ (U.valid.add_mem hV (U.valid.smul_mem _ (U.valid.smul_mem _ (U.valid.sub_mem hw hV)))) (by
    have he: ‖p‖=1/2:=by unfold p; rw [norm_smul,Real.norm_of_nonneg (by positivity)]; field_simp; rfl
    have hb:0 ≤ rower t:=t.property.1; have hu:rower t ≤ 1:=t.property.2; apply (norm_add_le ..).trans; rw [norm_smul, he, Real.norm_of_nonneg hb]; linarith)
  have ht t:∃ f α0 z,Tried V D Q Z ε m N (r t) f α0 z∧ (t=zeroT→f=x') ∧ (t=c→f=y'):=by
    by_cases hh:t=zeroT
    · subst t; rw [hz]; exact ⟨x',α,ρ,he,fun _=>rfl,fun h=>False.elim (hne h.symm)⟩
    by_cases hk:t=c
    · subst t; rw [hf]; exact ⟨y',δ,σ,he',fun h=>False.elim (hne h),fun _=>rfl⟩
    obtain ⟨w,a,p,hp⟩:= hp.pays _ _ he.time _ (hor t)
    exact ⟨w,a,p,⟨he.time,hor _,hp⟩,fun h=>False.elim (hh h),fun h=>False.elim (hk h)⟩
  choose W aQ z h1 h2 h3 using ht
  obtain ⟨hF,hL⟩:= queries (J:=Projection.straight rower) hZ _ r W aQ z h1 (sound _ _ hK he.time · 5) (fixed_read (fun i:Team=> 0) B he.time.le · 4)
  have hv := h.paid (Cube G) W (fun z' => ?_) (fun i=> (h1 i).run.toll) c zeroT
  · rw [h2 _ rfl,h3 _ rfl] at hv; change ‖_‖ ≤ (1/4:ℝ)*‖2*d-0‖ at hv; rw [Real.norm_of_nonneg (by linarith)] at hv; unfold d at *; linarith
  · have hk:=congr_arg Prod.fst (phase_bend (U:=fun i=> (W i,aQ i)) (organized B) _ b _ z' _ _ (fun i=> aligned (h1 i).run he.time B) hg hF hL); simpa only [Prod.fst_sum] using! hk
end YM.UVExtension.Reward
