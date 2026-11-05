import YM.TraceExtension.Anchor.Book

/-!
At an anchor level k, a supported exponential entry with mild marker cost is a local
borel coarse-lattice observable. Read it by its given back kernel (on the *Wilson
history*, before taking any physical/spacetime extension), at the fixed far-detector
clusterings. Obtain an approximating actual field with E subpower price over engineering,
at single-slot horizon d. This version also holds towards stage transitions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pull
open Set Function Analysis Filter Asymptotics MeasureTheory Extraction Around Table Lattice Wilson RG Next.UVStress MergeProof
  MergeProof.Accent Source Bid Extra.Histories Push Cells
open scoped Topology BigOperators ContDiff Classical
variable {G : Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}{d : ℕ}
variable (H:C.Makes){b:Ultrafilter (ℕ×ℕ)}(hb:(b:Filter (ℕ×ℕ)) ≤ f.fuse)
local notation "F"=> C.labels.level d
local notation "α"=> C.path.levels
local notation "A!"=> C.S.a
variable (Z : ∀ k _N p : ℕ, Coefficient (C.labels.level d) (C.side k p))
-- we keep per-stop height permissions in a separate prop.
def hosted : CutNet C:= fun k N p=> if h : k ≤ N then
      GridApprox.backTo C.path N p h (relayProbe C N k p d (Z k N p)) else 0
structure Costs (Q : ℕ→ℝ): Prop where
   calms : Calms C.S 0 Q
   pays : ∀ᶠ k:ℕ in atTop, 0<Q k ∧ ∀ᶠ i: ℕ×ℕ in (b:Filter (ℕ×ℕ)),
      let y:= Z k i.1 i.2
      let R:= C.path.rep i.1 i.2 k
      y.Format 0 C.params R ∧ ∃ e:ℝ, y.remBound 0 R (Real.sqrt (C.path.levels.clock.forcedAllowance k)) e∧ (C.labels.level d).coeffSize y.x+e ≤ Q k
structure Supported : Prop where
   exp : ∀ᶠ k:ℕ in atTop, ∀ᶠ i:ℕ×ℕ in (b:Filter (ℕ×ℕ)),profile (C.path.rep i.1 i.2 k).activities (Z k i.1 i.2).forced=0
   geometry : ∀ J:ℕ, ∀ᶠ k:ℕ in atTop, ∀ᶠ i:ℕ×ℕ in (b:Filter (ℕ×ℕ)), ∃ n:ℕ,Interior (GridApprox.window 0 n) (relayProbe C i.1 k i.2 d (Z k i.1 i.2)) ∧ GridApprox.room C.path.levels J k n
variable {W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{ζ:ℕ→ℕ→ℝ}{Doors:∀ N p i:ℕ,i<N→GaugeDoor (C.path.rep N p (i+1)) (C.path.rep N p i)}
variable (hr:Scrim C W u ψ φ δ ζ r Doors)

/-- finite witness part, including the bias receipt in actual exponential-jet coords. -/
def Captured (Q:ℕ→ℝ) (v:ℕ→ℕ×ℕ→C.label d):Prop:=
   ∀ᶠ k:ℕ in atTop, ∀ᶠ i: ℕ×ℕ in (b:Filter (ℕ×ℕ)), let T := C.factory d i.1 i.2
     let z:=(T.entries k (T.terminal.symm (v k i))).x
     let c:=(C.path.levels.params k).columns
     32*(1+c)^2*(C.labels.level d|>.coeffSize ((Z k i.1 i.2).x-z)) ≤ 2*(1+c)*Q k
include hr H hb
open GridApprox in
lemma acquired {Q:ℕ→ℝ}(hN : Costs (b:=b) Z Q) (hp:Supported (b:=b) Z) (K:Stock.Tabs C.path.levels):∃ v,
    Captured (b:=b) Z Q v∧∀ J:ℕ, ∃ E:ℕ→ℝ,Fast C.S E∧∀ᶠ k:ℕ in atTop,∀ᶠ i:ℕ×ℕ in (b:Filter (ℕ×ℕ)),∃ hN:J ≤ i.1,
       let T:= center C.S i.2 hN 0
       let q:= hosted Z k i.1 i.2- C.O i.1 i.2 (v k i) 0
       Interior (T.chamber 0) q ∧ T.rootTest (C.beta i.1 i.2) q ≤ E k:=by
   let e k:=4*(1+(α|>.params k).columns)*Q k
   have he: Calms C.S 0 e:= by
      let a : ℕ → ℝ:=fun i=>(C.path.levels.params i).columns
      have hx: Calms C.S 0 a:=column_calm _
      have hz(x:ℝ):Calms C.S 0 fun _=>x:=fun p hp=> factor_const _ _ p hp
      have hw:= ((hz 4).mul ((hz 1).add hx)).mul hN.calms; rw [add_zero,add_zero] at hw; exact hw
   let P(k:ℕ)(i:ℕ×ℕ)(x:C.label d): Prop:=∃ (h:k < i.1) (M:Music (F) C.path i.1 i.2), let J:=C.factory d i.1 i.2
      J.entries=(M.draft C.path).inits ∧ Sung (C.localSection d) C.path i.1 i.2 C.params W (C.ref d) M ∧ (∀ l:ℕ,C.ref d ≤ l→∀ hl:l < i.1, Carol (C.localSection d) C.path i.1 i.2 l (Doors i.1 i.2 l hl) (M.tone (l+1)) (M.tone l) (ψ l)) ∧
      (∀ y, profile (C.path.rep i.1 i.2 i.1).activities ((M.tone i.1).plays y).forced=hook (C.path.rep i.1 i.2 i.1).activities (C.path.rep i.1 i.2 i.1).p.threshold (booster (C.localSection d) (C.path.rep i.1 i.2 i.1) 0 y)) ∧
      ∀ m:ℕ,∀ w:ℝ,C.ref d ≤ m→m ≤ k→0<w→ w*‖alto C.path m d‖*(e k/gainChart C.path k m) ≤ ζ d m/2 → ∃ V t, FReach (φ:=φ) (ψ:=ψ) (ζ:=ζ) (D:=Doors) C i.1 k m i.2 d (Z k i.1 i.2) M (Q k) w V t (J.terminal.symm x) h.le
   have hx : ∀ᶠ k:ℕ in atTop,∀ᶠ i : ℕ×ℕ in (b:Filter (ℕ×ℕ)),∃ z,P k i z:=by
      filter_upwards [hN.pays,eventually_ge_atTop (C.ref d)] with k hg hB
      filter_upwards [(large_mesh f (k+1)).filter_mono hb,hg.2] with i hi hC
      obtain ⟨N,p⟩:= i; obtain ⟨hc',x,hX,hQ⟩:= hC; have ht:k<N:=hi
      obtain ⟨M,hM,hL,hc,hH⟩:= (hr.costs.aim d N p (hB.trans ht.le)).lyrics
      obtain ⟨v,hv⟩:= reaches C N k p d H (Z k N p) M x hr (Q k) (e k) ht.le hB hL hc hc' hX hQ le_rfl hg.1
      refine ⟨(C.factory d N p).terminal v,ht,M,hM,hL,hc,hH,fun m w h₁ h₂ h₃ h₄=>?_⟩
      specialize hv m w h₁ h₂ h₃ h₄; simp only [LinearEquiv.symm_apply_apply]
      exact hv
   let v(k:ℕ)(i:ℕ×ℕ): C.label d:=if h:∃ z, P k i z then Classical.choose h else 0
   have hv: ∀ᶠ k:ℕ in atTop,∀ᶠ i : ℕ×ℕ in (b:Filter (ℕ×ℕ)), P k i (v k i):= hx.mono fun k h=> h.mono fun i p=> by unfold v; rw [dif_pos p]; exact Classical.choose_spec p
   let price(m k):ℝ:=‖alto C.path m d‖*(e k/gainChart C.path k m); let cash(m k):ℝ:= (ζ d m/2)/price m k
   have hW(m:ℕ)(hm:C.ref d ≤ m): ∀ᶠ k:ℕ in atTop, 0 < cash m k ∧ cash m k * price m k ≤ ζ d m/2 :=by
      filter_upwards [hN.pays] with i hi; have h0:= hr.grows d m hm
      have hx: 0<price m i:=by
         unfold price; rw [alto_norm]; have hL:= lt_of_lt_of_le zero_lt_one (C.path.levels.params i).columns_ge; have ht:= hi.1; have hx:= C.S.a_pos m; unfold gainChart e; positivity
      exact ⟨div_pos (half_pos h0) hx,(div_mul_cancel₀ _ hx.ne').le⟩
   refine ⟨v,?_,?_⟩
   · let m:=C.ref d; filter_upwards [hv,hW m le_rfl,eventually_ge_atTop m] with k h0 hw hm
     filter_upwards [h0] with i ⟨hi,M,hM,hL,hA,hb',Hf⟩
     obtain ⟨V,t,hh⟩:= Hf m (cash m k) le_rfl hm hw.1 (by rw [mul_assoc]; exact hw.2)
     dsimp only; rw [hM,(show ∀ q,( (M.draft C.path).inits k q).x=(M.tone k).index q from (hL.earned k hm hi.le).currents)]; exact hh.bias
   intro J; let p:=max J (C.ref d); obtain ⟨m,hm⟩:= Stock.Tabs.mayOpen (α) 1 K J; let m':= max p m
   have hM': C.ref d ≤ m':=(le_max_right ..).trans (le_max_left ..)
   have ht:= Stock.Tabs.open_later (α) (show ℝ from 1) K hm (show m ≤ m' from le_max_right ..) zero_le_one
   let W(k):= stakes C J m' / cash m' k; refine ⟨W,?_,?_⟩
   · let q:= ζ d m'/2
     have hG :0<q:=half_pos (hr.grows _ _ hM'); let g :ℝ:=1/8
     let E := ‖alto C.path m' d‖ * stakes C J m' * factor C.S g m'/q
     have hf : W = (factor C.S (-g) * e) * (fun _=>E):=by
        funext k; unfold W cash price gainChart E factor; change _=Real.exp (_*-g)*_ * (‖_‖*_*Real.exp (_*g)/q)
        unfold g q; rw [div_div_eq_mul_div, mul_sub, Real.exp_sub, mul_neg, Real.exp_neg]; ring_nf; simp [inv_inv]; left; ring
     rw [hf]; exact ((show Fast C.S (factor C.S (-g)) from ⟨-g,by unfold g; norm_num,isBigO_refl ..⟩).mul he|>.mul (fun _ h=>factor_const _ _ _ h))
   filter_upwards [hv,hp.exp,hp.geometry J,eventually_ge_atTop m',hW m' hM'] with k hV hE hP hmk H₀
   have hY : ∀ᶠ i:ℕ×ℕ in (b:Filter _), ∃ hj : J ≤ i.1, ∀ q:C.label d, Interior ((center C.S i.2 hj 0).chamber 0) (C.O i.1 i.2 q 0):= by
      filter_upwards [ (RelayDifference.cutoff_grows f).eventually (Stock.clear_interior C H J d) |>.filter_mono hb] with i ⟨x,h⟩; exact ⟨x,h _ _⟩
   filter_upwards [hV,hE,hP,hY] with i Hx HE Hy Hw
   obtain ⟨N,p⟩:=i; obtain ⟨hm,hX⟩:=Hw; obtain ⟨n,hV,hR⟩:=Hy; obtain ⟨hi,M,hM,hL,hC,hD,hF⟩:= Hx
   have hm₀:= ht.1.trans hmk
   obtain ⟨V,t,hT⟩:= hF m' (cash m' k) hM' hmk H₀.1 (by rw [mul_assoc]; exact H₀.2)
   have hx:= foundation_quakes C N k m' p d H (cash m' k) _ M hr J K hi hM' hmk H₀.1 hT hL hC hD HE ht n hR hV
   let T:=C.factory d N p; let z:=v k (N,p); rw [show T.terminal (T.terminal.symm z)=z from T.terminal.apply_symm_apply _] at hx
   have hΩ: Interior ((center C.S p hm 0).chamber 0) (hosted Z k N p):=by
       have hq : Interior (GridApprox.window (GridApprox.anchor C.S p hm₀ 0) n) (relayProbe C N k p d (Z k N p)):= (show GridApprox.anchor C.S p hm₀ 0=0 from (C.S.toDepth hm₀ p).root.map_zero).symm ▸ hV
       rw [hosted,dif_pos hi.le]; exact (backTo_local C.path N p hm₀ hi.le 0 n hq).enlarges (room_fits p (α) n hm₀ hi.le hR _)
   refine ⟨hm,Next.UVStress.minus hΩ (hX _),?_⟩; dsimp only [Prod.fst] at *; unfold hosted; rw [dif_pos hi.le]; exact hx
end YM.Trace.Pull
