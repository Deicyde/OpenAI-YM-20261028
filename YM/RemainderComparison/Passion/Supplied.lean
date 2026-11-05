import YM.RemainderComparison.Passion.Seated
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Passion
open Function Filter Set Finset Lattice RG Wilson MeasureTheory Push Push.AbsoluteSums Marker
open Solos Mosaic Verse Serif Flues WickReps Ethereal Lacuna Lobby
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {θ ι:Type}{D :ι→ Finset θ}{Q:θ→Type*} [∀ i,NormedAddCommGroup (Q i)][∀ i,NormedSpace ℝ (Q i)]
variable {G:Gauge}{n:Side}{I:Type}
variable (T:Manor G n ι (Audited Q) I)(p:BudgetPoint)(R:ι→Support n)(Z:Set ι)
open Source Labels Next.Foundations Local Work.G08 AnalyticBridge VerifiedReset VerifiedReset.Seat
namespace SeatD
variable (S:SeatD G n) (X:Hol G) (K:Support n) (M:MaskType)
local notation "F"=> S.basis
local notation "A"=> S.sectionQ
local notation "o" => S.origin
local notation "v" => p.threshold
local notation "S₁"=> S.suit
local notation "S₂" => seeing S K M
local notation "Y"=> Local.joint A o K
structure Core (x:PairD S): Prop where
   header : S.realD x.header
   salt : p.Regular (seeing S K M) (fun V=> ((chord p S x.header V).re))
   regular : p.Regular (Local.joint S.sectionQ S.origin K) x.entry
   exactQ : Reads X S.origin (Local.joint S.sectionQ S.origin K) (0:Labels.Label G S.degree) (Complex.ofReal ∘ x.entry)
-- Costs at arbitrary x in enlarged support even canonical primary only masked on suit. using p actual not Seed alternate. 
structure Palette (x:PairD S)(x':Site n) (c:ℝ):Prop where
   termsC : S.basis.coeffSize x.header ≤ c
   core : p.supBounds x' (Local.joint S.sectionQ S.origin K) x.entry c
   astro : p.supBounds x' (seeing S K M) (fun V=> ((chord p S x.header V).re)) c
open PhysicalNext.Repeat Trio
lemma fluid (U:ℝ) (g:Config G n→ℝ)(X:Support n)(hp:LocalOn X g)(he:GaugeInvariant g)(hh:Measurable g)(hu: p.threshold=U): Trio.Tidy p X (masked U X g):=by
    subst U; refine ⟨fun U V h ht=> ?_,masked_measurable _ _ _ hh,fun s U=> ?_⟩
    · have hV : Healthy v X U ↔ Healthy v X V:=by unfold Healthy; rw [Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_iff_inter_eq_empty, ht]
      by_cases ha:Healthy v X U
      · rw [masked_eq _ _ _ _ ha,masked_eq _ _ _ _ (hV.1 ha)]; exact hp U V h
      rw [masked_ne _ _ _ _ ha,masked_ne _ _ _ _ (mt hV.2 ha)]
    by_cases hp:Healthy v X U
    · rw [masked_eq _ _ _ _ hp,masked_eq _ _ _ _ (?_ : Healthy _ _ (Lattice.gauge s U))]; exact he s U
      unfold Healthy; rw [gauge_flags]; exact hp
    rw [masked_ne _ _ _ _ hp,masked_ne _ _ _ _ (?_ : ¬ Healthy _ _ (Lattice.gauge s U))]; unfold Healthy; rw [gauge_flags]; exact hp
lemma Core.note {x:PairD S} (h:Core p S X K M x) : Trio.Tidy p Y (SeatD.sharp p S K M x):=by
    have ht:= Passion.SeatD.fluid p _ _ _ h.salt.sites h.salt.symmetry h.salt.borel rfl; have hz:= Passion.SeatD.fluid p _ _ _ h.regular.sites h.regular.symmetry h.regular.borel rfl
    have h_add {f g:Config G n→ℝ}(h:Tidy p Y f)(hh:Tidy p Y g): Tidy p Y (fun i=>f i+g i):=⟨fun Xu B hx hy=>congr_arg₂ _ (h.uses Xu B hx hy) (hh.uses Xu B hx hy), h.borel.add hh.borel, fun i j=> congr_arg₂ _ (h.invariant i j) (hh.invariant i j)⟩
    refine h_add (h_add (Trio.tidy_const p _) ?_) hz
    exact ⟨Work.H03.reads_larger (primary_composes S K M).2 ht.uses,ht.borel,ht.invariant⟩
variable (U:Config G n) (f: Config G n→ℝ){c:ℝ}
variable (h:Local.Readable X S.sectionQ p n c)
include h
-- geometry requirement that EXACT input-root site from basis.B.Support any. projection.Read OK. no appeal to dynamical budget unless separately earned.
omit h in
lemma prices {x : PairD S}{w:ℝ}(hP:Palette p S K M x o w) : ‖sharp p S K M x U‖ ≤ 3*w:=by
   have h_: ‖(x.header 0).re‖≤ w:= (Complex.abs_re_le_norm (x.header 0)|>.trans ((norm_le_pi_norm (G:=fun _ : S.basis.Index=> ℂ) _ _).trans ((norm_le_size F _).trans hP.termsC))) -- edit
   have hp:= hP.astro; have hv:=hP.core; unfold sharp
   apply (norm_add_le ..).trans; apply le_trans (add_le_add ((norm_add_le ..).trans (add_le_add h_ (AnalyticBridge.CouplingShape.mask_cost hp _))) (AnalyticBridge.CouplingShape.mask_cost hv _)); linarith
variable (hh:p.Regular K f)
omit h
def cx (f:Config G n→ℝ): Config G n→ℂ:= Complex.ofReal ∘ f
local notation "W"=> weighted X F o K v (cx f)
def sector : PairD S := ⟨W, fun U => ((Push.Local.residual X A o K v (cx f) U).re)⟩
def pure (x:ℝ): PairD S:= ⟨(↑x:ℂ) • S.basis.e0,0⟩
include h hh
local notation "A'"=> sector p S X K f
local notation "Q₁"=> Push.Local.residual X A o K v (cx f)
lemma moondrop : S.realD W:=by
   have he:star (cx f)=cx f:=by ext i; simp [cx]; -- ext complex? edit
   exact (congr_arg (weighted X F o K v) he.symm).trans (Local.weighted_star X F o v (show p.Regular K (cx f) from regular_mapped Complex.ofRealCLM hh) h.order)
lemma furnished : Q₁ = cx ((A').entry):=by
   have hw :=earthly p S X h (moondrop p S X K f h hh); funext U
   apply Eq.symm; change (↑((Q₁ U).re):ℂ)=_; apply reality; unfold Local.residual; simp only [Pi.sub_apply,star_sub, show star ((cx f) U)= (cx f) U from (by simp [cx])]; rw [← hw U]
omit hh in
lemma irrigated : p.Regular (S₂) (fun V=> (S.chord p W V).re):= CouplingShape.reg_extend (regular_mapped Complex.reCLM ((Local.presented_good o h (S.basis.core W)).1)) (primary_composes S K M).1
lemma sector_core : Core p S X K M A':=by
    obtain ⟨hr,hp,hT,hU⟩:= Local.convert_atom o h (regular_mapped Complex.ofRealCLM hh)
    exact ⟨moondrop p S X K f h hh,irrigated p S X K M f h,regular_mapped Complex.reCLM hr, (show Reads X S.origin Y (0: Labels.Label G S.degree) (cx (A').entry) from (furnished p S X K f h hh) ▸ hT)⟩ -- proof casts
local notation "b"=> Local.atomPrice X F c
lemma sold {w:ℝ}(hq:p.supBounds o K f w): Palette p S K M (sector p S X K f) o (b*w):=by
    have hζ := sector_core p S X K M f h hh
    have hc : p.Regular K (cx f):= regular_mapped Complex.ofRealCLM hh
    have he : p.supBounds o K (cx f) w:= (sup_real hh).mpr hq
    have hv:= (Local.weighted_bound X F o hc h.order h.power he)
    have hp:= h.nonneg; have hW:= hq.1
    have ht:= readPrice_pos X F
    have hC:c*readPrice X F ≤ b:=by unfold atomPrice; nlinarith only [ht]
    refine ⟨hv.trans (mul_le_mul_of_nonneg_right (show readPrice X F ≤ b by unfold atomPrice;nlinarith) hW), (sup_real hζ.regular).mp ?_,(sup_real hζ.salt).mp ?_⟩
    · change p.supBounds o Y (cx _ ) _; rw [← furnished p S X K f h hh]; exact (Local.charge_atom o h hc he).1
    rw [show (fun U=> (↑(SeatD.chord p S (A').header U).re : ℂ))= SeatD.chord p S W from funext fun U=>reality _ (earthlyC p S X h hζ.header U)]
    apply bound_larger (f:=Local.presented S.sectionQ o p.threshold (S.basis.core W)) _ (primary_composes S K M).1
    exact bound_weaken (Local.presented_good o h _).2 ((mul_le_mul_of_nonneg_left ((size_core ..).trans hv) hp).trans (by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hC hW))
lemma dayAgree (hp:Healthy p.threshold Y U) : RG.masked v K f U=sharp p S K M A' U:=by
    have hM(Scope:MaskType) : RG.masked v (S.seeing K Scope) (fun V=> ((SeatD.chord p S (A').header V).re)) U= (SeatD.chord p S W U).re := RG.masked_eq _ _ _ _ (hp.mono_left (primary_composes S K Scope).2)
    rw [show sharp p S K M A' U= sharp p S K .exactM A' U from (by unfold sharp; rw [hM,hM]),RG.masked_eq _ _ _ _ (hp.mono_left Finset.subset_union_left)]
    refine Complex.ofReal_injective ?_; rw [plucked p S X K A' U h (moondrop p S X K f h hh), masked_eq _ _ _ _ hp]; have he : Local.rebate X A o K v (cx f) U=0:= (Local.convert_atom o h (show p.Regular K (cx f) from regular_mapped Complex.ofRealCLM hh)).2.2.2.healthy_zero U hp
    change masked p.threshold K (cx f) U-_ -masked p.threshold Y Q₁ U=0 at he; rw [masked_eq _ _ _ _ hp, masked_eq _ _ _ _ (hp.mono_left Finset.subset_union_left)] at he; have hg:= furnished p S X K f h hh; rw [hg] at he; refine (eq_add_of_sub_eq (sub_eq_zero.mp he)).trans (add_comm ..)
end SeatD
end YM.RemainderComparison.Passion
