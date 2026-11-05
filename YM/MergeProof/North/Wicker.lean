import YM.MergeProof.North.Bonus
import YM.MergeProof.North.GraceN


set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Function Filter Lattice RG MeasureTheory Asymptotics Finset Bid
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Bandage PhysicalNext.Repeat.Mallow
open scoped Topology BigOperators Classical
variable {G:Gauge}(C:Family G)(d:ℕ)(hG:G.Simple)
local notation "P"=>C.path.levels
local notation "Q"=>C.S.scale
set_option quotPrecheck false
local notation "δ"=> renal C.path.levels
local notation "η"=> near C.path.levels
local notation "J"=> C.path.levels.budget
local notation "H"=> C.path.levels.clock.hatBeta
lemma futon : Note C.S (fun i=> ∏ m∈range i,(C.path.levels.params (m+1)).columns) 0:=by
   have hp(i):0<(C.path.levels.params i).columns:=zero_lt_one.trans_le (C.path.levels.params i).columns_ge
   have he:= Work.I04.columns_receipt (P)|>.tendsto_div_nhds_zero
   refine ⟨fun i=>prod_pos fun m _=>hp _,he.congr' (Eventually.of_forall fun i=> ?_)⟩; dsimp only; rw [Real.log_prod (fun m _=> (hp _).ne')]
lemma fuNote : Note C.S (fun i=>(C.path.levels.params i).columns) 0:=by
   let p i:=(C.path.levels.params i).columns; let a i:= ∏ m∈range i,p (m+1)
   refine ⟨fun i=>zero_lt_one.trans_le (C.path.levels.params i).columns_ge,tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (show Tendsto (fun i=> Real.log (a i)/Q i) atTop (𝓝 0) from (futon C).pitch) ?_ ?_⟩
   · exact Eventually.of_forall fun i=> div_nonneg (Real.log_nonneg (C.path.levels.params i).columns_ge) (Shoot.scale_nn (C.path.levels) _)
   filter_upwards [eventually_gt_atTop (0:ℕ)] with i hi
   have hf:p i≤a i:=by
      cases i; omega
      unfold a; rw [Finset.prod_range_succ]; exact le_mul_of_one_le_left (zero_le_one.trans (C.path.levels.params _).columns_ge) (Finset.one_le_prod fun k _=> (C.path.levels.params (k+1)).columns_ge)
   exact div_le_div_of_nonneg_right (Real.log_le_log (zero_lt_one.trans_le (C.path.levels.params _).columns_ge) hf) (Shoot.scale_nn _ _)
include hG
lemma hut : Note C.S (H) 0:= ⟨fun i=>zero_lt_one.trans (C.path.levels.fits.delayed i),(Work.I04.hat_receipt _ hG).tendsto_div_nhds_zero⟩
lemma mintN : Note C.S δ 0 ∧ Note C.S η 0:=by
   have he: Note C.S (fun i=> H (i+1)) 0:= (hut C hG).scales C.path.levels.fits.mesh
   refine ⟨(he.powr (-2)).swapP (mul_zero _),?_⟩
   have ht:= (Note.notes C.S 1 zero_lt_one).splits he; unfold near sap; simpa only [one_div,sub_zero] using! ht -- sap maybe not ns
lemma plumN (a:ℝ)(ha:0<a): Note C.S (Accent.plumR C d a) (-d):=by
   let v i:= (P|>.params i).columns
   have hp : Note C.S (Mix.envelope C a) 0:= (((Note.notes C.S a ha).mills (fuNote C)).mills (futon C)).swapP (by norm_num)
   have hx : Note C.S C.path.levels.clock.hatCoupling 0:= by
      have h : Note C.S (fun i=> Real.sqrt (H i)) 0:=by
          simp_rw [Real.sqrt_eq_rpow]; exact ((hut C hG).powr _).swapP (by norm_num)
      have he:= (Note.notes C.S 1 zero_lt_one).splits h; simpa only [sub_zero,one_div] using! he
   -- η order
   apply (((Note.note_a C.S|>.powerN d).mills ((hx.powerN _).splits hp)).swapP ?_)
   simp
-- need exp using logBeta.scale
lemma whence : Tendsto (fun i=> Real.sqrt (H i)/C.S.scale i) atTop (𝓝 0):=by
   have ht : Tendsto (H) atTop atTop:= tendsto_atTop_add_const_left _ _ (C.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos hG))
   have he:Tendsto (fun i=> H i / C.S.scale i) atTop (𝓝 G.slopeConstant):= by
       have hp : Tendsto (fun i=> C.path.levels.clock.bar/C.S.scale i) atTop (𝓝 0) := tendsto_const_nhds.div_atTop C.S.divergent
       refine (show Tendsto (fun i=> C.path.levels.clock.bar/C.S.scale i+G.slopeConstant) atTop (𝓝 G.slopeConstant) from by simpa only [zero_add] using! hp.add_const G.slopeConstant).congr' ?_; filter_upwards [C.S.divergent.eventually_gt_atTop 0] with i hi; change _= (C.path.levels.clock.bar+G.slopeConstant* Q i)/_; rw [add_div,mul_div_cancel_right₀ _ hi.ne']
   have hx:Tendsto (fun i=> (Real.sqrt (H i))⁻¹) atTop (𝓝 0):=by simp_rw [Real.sqrt_eq_rpow]; exact tendsto_inv_atTop_zero.comp ((tendsto_rpow_atTop (by norm_num)).comp ht)
   refine (show Tendsto (fun i=> H i/Q i*(Real.sqrt (H i))⁻¹) atTop (𝓝 0) from by simpa using! he.mul hx).congr' ?_
   filter_upwards with i; let y:=H i; have hp: 0<y:=zero_lt_one.trans (C.path.levels.fits.delayed _); have hf:= Real.mul_self_sqrt hp.le; change y/_*(Real.sqrt y)⁻¹= Real.sqrt y/_; nth_rw 1 [← hf]; have hv:0<Real.sqrt y:= Real.sqrt_pos.2 hp; ring_nf; field_simp
lemma banket : Note C.S (bling (P)) 0:=by
   have ht : Note C.S (fun i=> Real.exp (Real.sqrt (H i))) 0:= ⟨fun i=>Real.exp_pos _,by simpa only [Real.log_exp] using! whence C hG⟩
   exact ht.scales C.path.levels.fits.mesh
variable {r:ℕ→ℕ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)} -- check
variable (hV:Velour C (renal C.path.levels) r D)
include hV
local notation "K"=> (fun i=> ((J i).supportExponent+1/2)*peepers C.path.levels i)
lemma whack : Tendsto (fun i=>K i /Q i) atTop (𝓝 0):=by
   have hp:= banket C hG|>.pitch; unfold bling at hp; simp only [Real.log_exp] at hp
   apply squeeze_zero' _ _ hp
   · exact Eventually.of_forall (fun i=>div_nonneg (mul_nonneg (add_nonneg (C.path.levels.budget i|>.exponent_pos.le) (by norm_num)) (by exact_mod_cast Nat.zero_le _)) (Shoot.scale_nn _ _))
   exact Eventually.of_forall fun i=> div_le_div_of_nonneg_right (hV.costs i) (Shoot.scale_nn _ _)
lemma billed : Note C.S (fun i=> Real.exp (K i)) 0:= ⟨fun i=> Real.exp_pos _,by simpa only [Real.log_exp] using! whack C hG hV⟩
lemma briar : Note C.S (fun i=> ((J i).B:ℝ)) 0:=by
   have he(i): (1:ℝ)≤ (J i).B:=by exact_mod_cast (J i).B_pos
   have ht(i):0 ≤ Q i:=Shoot.scale_nn C.path.levels i
   refine ⟨fun i=>zero_lt_one.trans_le (he i), tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (whack C hG hV) (Eventually.of_forall fun i=>div_nonneg (Real.log_nonneg (he i)) (ht i)) ?_⟩
   filter_upwards with i
   let x:ℕ:= (J i).B; let q:ℕ:= (2*(1024*x)+1); have hp: 2*x ≤ peepers C.path.levels i:= le_trans (show 2*x ≤ q by unfold q; omega) (by change q ≤ q^4; have hz:1≤q:=Nat.le_add_left ..; exact (le_of_eq (pow_one q).symm).trans (pow_le_pow_right₀ hz (by decide)))
   have hv:(2:ℝ)*x≤peepers C.path.levels i:=by exact_mod_cast hp
   refine div_le_div_of_nonneg_right ((Real.log_le_self (show 0 ≤ (x:ℝ) from by positivity)).trans ?_) (ht i)
   linarith only [hv,mul_nonneg (J i|>.exponent_pos.le) (Nat.cast_nonneg (α:=ℝ) (peepers C.path.levels i))]
lemma fuchsia : Note C.S (fun i=> fuga (P) i) (-1):= ((Note.notes C.S 128 (by norm_num)|>.mills ((briar C hG hV).powerN 2)).mills (Note.note_a C.S)).swapP (by ring)
end YM.MergeProof.Ribbons
