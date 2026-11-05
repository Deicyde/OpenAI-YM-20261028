import YM.RG08.Town.Tau
/-!
# Transmit in a polynomial moment path. No recomputing constant sectors as free forcing.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.RG08.Town
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect Work.F08 Push.AbsoluteSums Matrix
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Staffer PertExtension.Series.Radial PertExtension.Series.Tested Pill Wings
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {I J:Type}{u : I→Windows}{w:J→ShoreP u}{X:Chain}{G:Gauge}{E e n r d τ D j k t ε:ℕ}{ν:G.ColorIndex}{F:Labels.Frame G d}{Ω:SectionData F}{H:Hol G}{D':ChartRatio G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}{R:ℝ}{h:1/2≤R}{hD:d+1≤D}{T:Signals P Q E τ H Ω h hD}{A:Grotto G P k E τ}
variable {M : Wall w 1→ Wings u 1} {ρ : ∀ i:Wall w 1,Site (X.S.block (M i).i)} {p b:J→ℝ} {δ : Wall w 0→ℝ} {U V:Wall w 0→ Tale G}
local notation "Γ" => heights (u:=u) X ν D'
local notation "Ⓨ" => wallY X
local notation "Λ" => strideP X w
structure Arbor (X:Chain)(w:J→ ShoreP u)(δ : Wall w 0→ℝ): Prop where
  pos : 0≤δ
  one : δ≤1
  tell :∀ i: Wall w 1, δ i.low / (X.S.block i.i).val ≤ δ i.roof
structure Tie (V:Wall w 0→ Tale G) (X:Chain)(ν:G.ColorIndex)(σ:ChartRatio G)(ε:ℕ)(M:Wall w 1→ Wings u 1) (ρ:∀ i:Wall w 1,Site (X.S.block (M i).i)):Prop where
   here (i): (M i).toLaunch=i.world.toLaunch
   stone (i): Stone ε (V i)
   sewn (i:Wall w 1): V i.low=inscribed ε (heights X ν σ (M i)) (ρ i) (V i.roof)

lemma sapling (hp:Pines A u)(he:Tights T S ν D' u)(hx:∀ i, (M i).toLaunch=i.world.toLaunch)(ho:Arbor X w δ)(h:∀ i:Wall w 0,Stone ε (U i))(hE:e≤ E)(hτ:ε ≤τ)(hr:r≤ε+e)(hg:r≠0)(hq:0≤p) (hk:Card k (fun j=>Ⓨ (Wall.tip w j)) p (fun i=>U (Wall.tip w i) e r) (fun i=>δ (Wall.tip w i)))
    (hT: ∀ i<e,∀ j,j≠0→ Card k Ⓨ (Λ p) (fun t=> U t i j) δ)
    (hM: Card k Ⓨ (Λ p) (fun t:Wall w 1=> U t.low e r-holdP (ρ t) (Γ (M t)).tree (U t.roof e r)) (fun t=> δ t.low)): Card k Ⓨ (Λ p) (fun t=> U t e r) δ:= by
   let P i:= holdP (ρ i) (babyQ G X (M i)) (U i.roof e r); let F i:= polishS (U i)
   have hV: Card k Ⓨ (Λ p) (fun t:Wall w 1=> holdP (ρ t) (Γ (M t)).tree (U t.roof e r)-P t) (fun t=>δ t.low) := by
     have hK:= lensCall he hx k; have hs : Weighed Ⓨ (fun i:Wall w 1=> ((X.S.block i.i).val:ℝ)):= by
         rw [show (fun i:Wall w 1=> ((X.S.block i.i).val:ℝ))=(fun i:Wall w 1=> ((X.S.block (M i).i).val:ℝ)) from funext fun i=>by rw [show (M i).i=i.i from congr_arg Launch.i (hx i)]]; exact hK.pay
     unfold P; simp_rw [← fun (i:Wall w 1) => polS_pos (i:=e) hg (U i.roof)] -- rewrites loop risk?
     refine curtain he hx (fun i=>jewel_stone (h i.roof)) hr ho.pos ho.one ho.tell ?_
     intro i hi j; by_cases hh:j=0
     · subst j; simp_rw [polish_dark]; exact Card.zero
     simp only [polishS,pebble,hh,↓reduceIte,sub_zero,Pi.sub_apply]; exact (hT i hi j hh).up hs hq
   apply traverse (Q:=P) hq ho.pos hk _ ?_; swap
   · rw [show (fun i:Wall w 1=> U i.low e r-P i)=(fun i:Wall w 1=> U i.low e r-holdP (ρ i) (Γ (M i)).tree (U i.roof e r))+(fun i=>holdP (ρ i) (Γ (M i)).tree (U i.roof e r)-P i) from funext fun i=>(sub_add_sub_cancel ..).symm]; exact hM.more hV (fun t=>ho.pos t.low) (Wall.plusOne _)
   intro i C ht; unfold P; have hf:(M i).i=i.i:=congr_arg Launch.i (hx i)
   have hh:gain X.S (1/2) i.i (i.i+1)=gain X.S (1/2) (M i).i ((M i).i+1):=by rw [hf]
   rw [hh]; exact tappedL hp he _ _ _ (h i.roof|>.tidy e r) hg (by omega) C _ _ ht (ho.pos _) (ho.one _) (by rw [hf]; exact ho.tell i)
lemma tapping (hp:Pines A u)(he:Tights T S ν D' u)(ht:ε ≤ τ)(hv:Tie V X ν D' ε M ρ)(hz:Arbor X w δ)(hk:e≤ E)(hx:0≤p)(hh:r≠0)
    (hY: ∀ i≤ E,∀ r,r≠0→ Card k (fun i=>Ⓨ (Wall.tip w i)) p (fun j=> V (Wall.tip w j) i r) (fun t=>δ (Wall.tip w t))): Card k Ⓨ (Λ p) (fun j=> V j e r) δ := by
   have hs i:= hv.here i; let B:= lensCall he hv.here k; have ha t : δ (Wall.low (b:=w) t)/(X.S.block (M t).i).val≤δ t.roof:= by rw [show (M t).i=t.i from congr_arg Launch.i (hs t)]; exact hz.tell t
   have hn i r (h:r>ε+i): Card k Ⓨ (Λ p) (fun t=>V t i r) δ:= by simp_rw [show ∀ j,V j i r=0 from fun j=>not_ne_iff.mp (mt ((hv.stone j).cap i r) (by omega))]; exact Card.zero
   revert hh; refine tribes_ind (k:=ε) hk (fun i r=>r≠0→ Card k Ⓨ (Λ p) (fun t=>V t i r) δ) ?_ (fun i _ r hp h=> hn i r hp) -- argument order
   intro i hi r hV h0; by_cases hg:r≤ε+i; swap; · exact hn i r (by omega)
   refine sapling (ρ:=ρ) hp he hv.here hz hv.stone hi ht hg h0 hx (hY i hi r h0) (fun j hj k' hh=> hV _ k' (Or.inl hj) hh) ?_
   let U t:=polishS (V t); have hP (a:Wall w 0) := jewel_stone (hv.stone a)
   rw [show (fun t:Wall w 1=> V t.low i r-holdP _ _ _)= (fun t=> coreT ε (Γ (M t)) (ρ t) (U t.roof) i r) from funext fun t=> by rw [hv.sewn]; unfold coreT U; rw [puzzleS _ (hv.stone _) (B.one _) h0, polS_pos h0]]
   refine (core_b (M:=fun i=>Γ (M i).wingR) (U:=fun i=> U i.roof) (A:=fun i=> U i.roof) (K:=fun i=>Γ (M i)) (z:=ρ) B hi ht (v:=fun t=>δ t.low) (fun i=>hz.pos _) (fun i=>hz.one _) ha (ρ:= Λ p) (fun i=>mul_nonneg (hx _) (gain_pos ..).le) (fun i=>hP _) (fun i=>hP _) ?_).first
   intro a b he; by_cases ht:b=0
   · subst b; simp only [U,polish_dark]; exact Drum.zero
   have hS : Weighed Ⓨ (fun i:Wall w 1=> ((X.S.block i.i).val:ℝ)):= by
      rw [show (fun i:Wall w 1=> ((X.S.block i.i).val:ℝ))=(fun i:Wall w 1=> ((X.S.block (M i).i).val:ℝ)) from funext fun i=>by rw [show (M i).i=i.i from congr_arg Launch.i (hs i)]]; exact B.pay
   simp only [U,polishS,pebble,ht,↓reduceIte,sub_zero,Pi.sub_apply]; exact Drum.home ((hV _ _ he ht).up hS hx)
lemma waist (hx:0≤p)(h: Card k Ⓨ (Λ p) (fun j=> V j e r) δ) : Card k Ⓨ (badge p) (fun j=> V j e r) δ:= h.raise (fun t=> by
   have he:0 ≤ X.S.scale (w t.a).next.i-X.S.scale t.i:= sub_nonneg.mpr (age_scale_mono _ t.last)
   have hh: gain X.S (1/4) t.i (w t.a).next.i ≤ 1:= Real.exp_le_one_iff.mpr (by nlinarith [mul_nonpos_of_nonpos_of_nonneg (by norm_num : -(1/4:ℝ)≤0) he])
   exact mul_le_of_le_one_right (hx _) hh)
theorem mittens (hp:Pines A u)(he:Tights T S ν D' u)(ht:ε ≤ τ)(hv:Tie V X ν D' ε M ρ)(hz:Arbor X w δ)(hk:e≤E)(hx:0≤p)
    (hS:∀ i≤E,∀ r,Card k (fun i=>Ⓨ (Wall.tip w i)) p (fun j=> V (Wall.tip w j) i r) (fun t=>δ (Wall.tip w t))) : Card k Ⓨ (badge p) (fun i=> V i e r) δ := by
   have hh(i)(hi:i≤E)(r)(hh:r≠0):= waist hx (tapping hp he ht hv hz hi hx hh fun i hi r _=>hS i hi r)
   by_cases h0:r=0; swap; · exact hh _ hk _ h0
   subst r; induction e using Nat.strong_induction_on with
   | h e ih=>
     apply signify (A:=fun i: Wall w 0=> V i e 0) (hS _ hk 0) hx hz.pos
     let Z := lensCall he hv.here k
     rw [show (fun i:Wall w 1=> V i.low e 0-V i.roof e 0)=(fun i=>coreT ε (Γ (M i)) (ρ i) (V i.roof) e 0) from funext fun i=>by rw [hv.sewn]; unfold coreT holdP; rw [slateS _ _ _ (hv.stone _|>.tidy _ _) (Z.one i|>.ct)]]
     refine (core_b (U:=fun i=> V i.roof) (A:=fun i=> V i.roof) Z hk ht (v:=fun t=> δ t.low) (w:=fun t=>δ t.roof) (fun i=>hz.pos _) (fun i=>hz.one _) (fun i=>by rw [show (M i).i=i.i from congr_arg Launch.i (hv.here i)]; exact hz.tell i) (ρ:=badge p) (fun t=>hx _) (fun i=> hv.stone _) (fun i=>hv.stone _) (r:=0) (z:=ρ) ?_).first
     intro i j hT; by_cases hr:j=0
     · subst j; have hg:i<e:= by unfold awaits at *; split_ifs at * <;> omega
       exact Drum.home ((ih _ hg (by omega)).mold Wall.roof)
     exact Drum.home ((hh i (by unfold awaits at hT; omega) j hr).mold Wall.roof)
end YM.RG08.Town
