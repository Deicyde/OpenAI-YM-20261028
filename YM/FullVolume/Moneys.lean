import YM.FullVolume.Lit

/-!
# Full-mesh all-period real separated bounds for canonical lattice differences

Buy the projected coefficient cost **before** taking any limits.
Uses cancellation inside the *literal Wilson laws*, including importantly
that an exact equation term has **zero rootTest** for the number of copies
being asked for at these scales.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume
open Function Filter Set MeasureTheory Metric Lattice RG Wilson Extraction Extraction.Lease Difference Gaps Cells Next.Rank Next.Rank.Market Push.RelayDifference
open Next.Extract MergeProof
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G:Gauge}{C:Family G}{S:Table C.book}{d : ℕ}{Y:Columns C S d} (T:Y.Trials) (M:C.Makes)(B:Stock.Tabs C.path.levels)(hp: Wcmain C) (h:VitalRank T)
    (V:∀ d,Source.SectionData (C.labels.level d))(R:Push.Mark.Weave G)(hV: ∀ d:ℕ,Push.Mark.Portfolio C.params (V d) (R d))
    {P:∀ d,Cutoffs→ (C.label d≃ₗ[ℂ] C.label d)} (a: Presentation C){ζ:ℕ→ℕ→ℝ}(hf:Hearthside C V R P a ζ)

include T M B hp h V R hV hf

theorem cap (F:Trial C)(l:List Axis)(hF:Funded F)(hw:∀ N p x,Continuous (F N p x))(x:Bid.Rowe C d)(hx:Coin C x)(u:Cutoffs→ℝ)(hu:Owed (Bid.upper C x - hops F l) u)(hL:Tendsto u mesh (𝓝 0)) : ∃ A:ℝ, ∀ᶠ i in mesh, ‖display a x i‖ ≤ A:=by
  obtain ⟨k,hk⟩:= (trained T M B hp h V R hV a hf l).exists
  obtain ⟨b,⟨Z,hZ,hB⟩,hM,hS⟩:= (hk.and (invites T M hp l h.shops k)).exists
  obtain ⟨v,hv⟩:=hM F hF hw
  let L (i):= probe T k i b l
  -- absolute boundedness of tested x (even before pricing the equation part)
  have he : ∃ c:ℝ, 0≤c ∧ ∀ᶠ i in mesh, ‖L i (x i)‖ ≤ c:=by
    let c := max 0 v+1
    refine ⟨c,by unfold c; positivity,?_⟩
    have hz:= hS _ _ hu hL
    filter_upwards [hv,(hz.norm.eventually (ge_mem_nhds (show ‖(0:FullVolume.Size Y.amount)‖ < 1 by simp))),hops_solid (F:=F) (Eventually.of_forall (fun i=> hw _ _)) l] with i hi hj hW
    have hg:=probe_sub T k i b l (Bid.upper C x) (hops F l) (fun s=> C.continuousO ..) hW
    change ‖assay T k i b l (Bid.upper C x - hops F l)‖ ≤ _ at hj; unfold L; rw [probe_eq]; rw [hg] at hj
    have hq:=norm_sub_norm_le (assay T k i b l (Bid.upper C x)) (assay T k i b l (hops F l))
    unfold c; linarith only [hi,hj,hq,le_max_right 0 v]
  obtain ⟨c,hC,he⟩:=he
  let X:= display a x
  let f i:ℂ:= ((1+‖X i‖ : ℝ):ℂ)⁻¹
  let y:Bid.Rowe C d:=fun i=> f i • X i
  let z:Bid.Rowe C d:=fun i=> f i • (x i-X i)
  have hz i : ‖f i‖=(1+‖X i‖)⁻¹:= by unfold f; rw [norm_inv, Complex.norm_real,Real.norm_of_nonneg (by positivity)]
  have hz' i:0 < 1+‖X i‖:= add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg _)
  have hs:∀ i,‖f i‖ ≤ 1:= by intro i; rw [hz]; exact inv_le_one_of_one_le₀ (by simp)
  have hT:Coin C z:=by
    have hd: z=f • x - y:= funext fun i=> (show f i • (x i-X i)=f i • x i-f i • X i from smul_sub _ _ _)
    rw [hd]; apply Coin.sub (hx.scaled ((Sluggish.const (C:=C) (1:ℝ)).reduce (Eventually.of_forall (fun i=> by simp [hs])))) (Coin.from_bound M (A:=1) ?_)
    refine Eventually.of_forall (fun i=>?_); unfold y; rw [norm_smul,hz i,mul_comm,←div_eq_mul_inv,div_le_one (hz' _)]
    linarith
  have hD:= sweep M B V R hV a hf z hT (fun i=> by unfold z X display; rw [map_smul,map_sub,a.projected,sub_self, smul_zero])
  have hl:= hS _ _ hD (flown (by norm_num))
  have hM : Tendsto (fun i=> Z*‖L i (z i)‖) mesh (𝓝 0):=by
    unfold L; simp_rw [probe_eq _ _ _ _ _ z]; simpa only [norm_zero,mul_zero] using hl.norm.const_mul Z
  let A:= 2*Z*c+1
  refine ⟨A,?_⟩
  filter_upwards [hB,he,hM.eventually (ge_mem_nhds (show 0<(1/2:ℝ) by norm_num))] with i hi hp hu
  change ‖X i‖≤A
  have ht:= hi (x i); change ‖X i‖ ≤ Z * ‖L i (X i)‖ at ht
  change Z*‖L i (z i)‖ ≤ 1/2 at hu
  unfold z at hu; rw [map_smul,norm_smul,hz] at hu
  rw [← mul_left_comm, mul_comm (1+‖X i‖)⁻¹, ← div_eq_mul_inv,div_le_iff₀ (hz' _), map_sub,norm_sub_rev] at hu
  unfold A; linarith only [ht,mul_le_mul_of_nonneg_left hp hZ,hu, mul_le_mul_of_nonneg_left (norm_sub_norm_le (L i (X i)) (L i (x i))) hZ]

omit B V hV hf T hp h R M in
lemma fixed_cost {f:Trial C}{v:Cutoffs→ℝ}(h:Owed f v)(hv:Tendsto v mesh (𝓝 0)): Funded f:=
    ⟨fun _=>1,Affords.enlarged h (Eventually.of_forall fun _=>hv.eventually (ge_mem_nhds zero_lt_one))⟩

theorem improved {F:Trial C}{l:List Axis}(hF:Funded F)(hw:∀ N p x,Continuous (F N p x)) (x:Bid.Rowe C d)(hx:Coin C x)(u:Cutoffs→ℝ)(hu:Owed (Bid.upper C x - hops F l) u)(hL:Tendsto u mesh (𝓝 0)): Funded (hops F l):=by
   obtain ⟨Z,hZ⟩:= cap T M B hp h V R hV a hf F l hF hw x hx u hu hL
   let y:=display a x
   have he:= hx.sub (Coin.from_bound (p:=y) M hZ)
   have hg:= sweep M B V R hV a hf (x-y) he (fun i=> by unfold y display; dsimp only [Pi.sub_apply]; rw [map_sub, a.projected,sub_self])
   have hy:= fixed_cost hg (flown (by norm_num)); have hh:= fixed_cost hu hL
   have hx : Bid.upper C x= Bid.upper C y - -(Bid.upper C (x-y)):= by
     rw [sub_neg_eq_add]; funext i j o; change C.O _ _ (d:=d) (x _) _= C.O _ _ (d:=d) (y _) _ + C.O _ _ (d:=d) (_-_) _; rw [show C.O _ _ (_-_) _=(C.O i j (d:=d) (x (i,j)) o)-(C.O i j (d:=d) (y (i,j)) o) from ((C.linearO _ _ _ _).mk' _).map_sub _ _]; abel
   have hv:Funded (Bid.upper C x):=hx ▸ Funded.sub M (Funded.primaries M hp y hZ) hy.neg
   simpa only [sub_sub_cancel] using! Funded.sub M hv hh
end YM.FullVolume
