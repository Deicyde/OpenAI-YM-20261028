import YM.TraceExtension.Zn.Trail
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Zn
open Function Filter Matrix Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp
open Filch Turret Shepherd AnalyticBridge VerifiedReset Drupes Extra.Iteration SectorAffine Fen Kits Pills Loft
open scoped BigOperators Topology Classical
variable {F:ℝ→ℝ}{a b c:ℝ}{k:ℕ}{G:Gauge}
lemma priced {D:ℝ} (hd:0 < D) : ConstMass 0 (fun x=>countCost (Perfect.east x/D)):=by
    let C:= Real.exp (1/D*2) * (Nat.factorial 6:ℝ); let f(x):=(C*(D*Real.log x)^6)*2^4; have hp:0≤ C:=by positivity
    have hx: ConstMass 0 f:=( (mass hp|>.cop (((mass hd.le).cop logC).crop 6))).cop (mass (show 0 ≤ (2:ℝ)^4 by positivity)); apply hx.mono
    filter_upwards[eastP,eventually_gt_atTop (1:ℝ)] with x hx hv; let a:=(Real.log x)⁻¹ /D; have hh:0 < a:=div_pos hx.1 hd
    refine ⟨(count_pos hh).le,?_⟩; change countCost a ≤ C*(D*Real.log x)^6*2^4; unfold countCost; rw [div_eq_mul_inv, ← inv_pow, show a⁻¹=D*Real.log x from ?_]; swap; · unfold a; rw [inv_div,div_inv_eq_mul]
    have he:= Real.log_pos hv; unfold C; have ht:a≤1/D:=div_le_div_of_nonneg_right hx.2 hd.le; gcongr
lemma gelling (D:ℝ)(hd:0<D){G:Gauge}(j:ℕ): ConstMass 0 (fun x=> gable G (Perfect.east x/D) j):=
    ((mass zero_le_one).gather ((mass (Nat.cast_nonneg (Fintype.card (Loc G 1)))).cop (priced hd))).crop j
lemma rimt(k:ℕ)(D:ℝ)(hd:0<D): ConstMass 0 (fun x=> ramt k (Fin 2) (Perfect.east x/D)):=by
    let f(x):=Perfect.east x/D; have ht:ConstMass 0 (fun x=>countCost (f x/2)):=by
       unfold f; simp_rw[div_div]; exact priced (show 0<D*2 by positivity)
    have hp:ConstMass 0 (fun x=> (2:ℝ)^k / (f x/8)):=by
       unfold f; simp_rw[div_div,div_eq_mul_inv]; unfold Perfect.east; simp only[_root_.mul_inv_rev,_root_.inv_inv]
       refine (mass (by positivity)).cop ?_; apply ConstMass.cop _ logC; exact mass (mul_nonneg hd.le (by norm_num))
    unfold ramt; exact ((mass (cabD_n (k:=k))).cop ((((mass zero_le_one|>.gather hp).crop k).cop (mass cabD_n)).crop (Fintype.card (Fin 2)))).cop (ht.crop _)
lemma bnk: ConstMass 0 (fun x=> bankCost (radiusB x)):=by
    unfold bankCost; push_cast; exact (mass (Nat.cast_nonneg _)).cop (((mass (by norm_num)).cop (upperB.gather (mass (by norm_num)))).crop _)
lemma Tigh.smokes(h:Tigh F k):ConstMass 0 F:=by
    intro a ha; filter_upwards [Tigh.tight h (Nat.zero_le _)] with x hx; exact ⟨hx.1,(hx.2.trans (le_of_eq (by simp))).trans (wok a x ha.le)⟩
lemma heat_two(G:Gauge)(D:ℝ)(hd:0<D)(A:ℝ→ℝ)(C':ℝ→ℝ)(h:Tigh A (k+4))(hp: ConstMass a C'): Tigh (fun x=> vocation G (Perfect.east x/D) (A x) (C' x)) k:=by
    unfold vocation cumulus; simp_rw[div_div]; have ht:0 < D*5:=by positivity
    exact (( (( Tigh.fact h (2^ (4:ℕ)) (by norm_num)).fly (gelling (D*5) ht (G:=G) 3)).fly hp)).mult ((mass (Nat.cast_nonneg (Fintype.card (Loc G 1)))).cop (priced ht))
end YM.Trace.Zn
