import YM.UVExtension.Free.Response

/-! Common coherent roll and all lifted rows. No choice via convergence of a subsequence of bodies. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Free
open Filter Function Lattice Laurent Bloch Metric Exterior Matrix Precision RG Next.Free Craft Work.F08
open scoped Topology BigOperators Classical
variable {G : Gauge} {m n : Type} [Fintype m] [Fintype n] {L : Side}

lemma installations {V:ℕ→Cross L m n} (h : Sailing V) (c f : Side) (hc : f.val=c.val*L.val) :
    Arrives fun i=> installed ⟨L,hc⟩ (V i):= by
  let g: Ratio c f:= ⟨L,hc⟩; refine (h.2 c).post (T:=fun P=> submatrix P (splitCo g m) id) ?_; fun_prop

lemma from_installations {V:ℕ→Cross L m n} (h : ∀ (c f:Side) (hc:f.val=c.val*L.val), Arrives fun i=> installed ⟨L,hc⟩ (V i))
    (c : Side): Arrives fun i=> (V i).acts c := by
  let g : Ratio c (c*L):=⟨L,rfl⟩
  have H:= h c (c*L) rfl; let E:= splitCo g m
  refine (H.post (T:=fun P=> submatrix P E.symm id) (by fun_prop)).copy (Eventually.of_forall fun i=>?_)
  ext j k; simp only [installed,Matrix.submatrix_apply,id_eq]; rw [show splitCo _ m _=j from E.apply_symm_apply _]

variable (A : Levels G) (i : ℕ) (K : ℝ) (hK: 0<K)
local notation "L₀" => A.S.block i
local notation "P(" n ")" => destination A n i
local notation "j" => A.clock.J (i+1)
local notation "j'" => A.clock.J i

include hK
open Flight
lemma frames_sail {a b: Type} [Fintype a] [Fintype b] (g : Thread j j' a b) (h : Secured g) (e : ℕ)
    (he : ∀ p∈baseCube, p≠0 → ∀ l: Site L₀, Arrives fun n=> g (P(n)) p l):
    Sailing (fun n=> show Cross L₀ a b from meshBook g e [] (P(n))) := by
  obtain ⟨x,C,hx,hC,hp⟩:= h.bankCost (A.clock.adm (i+1)) e (u:=[]) (Nat.zero_le _)
  have hs : Stock (α:=fun _=>Co L₀ a) (β:=fun _=>b) (fun n : ℕ => (1:ℝ)) fun n=> meshBook g e [] (P(n)) := by
    let t:=C/((L₀).val:ℝ)^e; have ht:0<t:=by unfold t; positivity
    refine ⟨fun _=> zero_le_one, x,t,hx,ht,fun n=> ?_⟩; rw [mul_one]; have h:= hp (P(n)); simp only [List.length_nil,Nat.add_zero] at h; exact h
  refine Sailing.of_read (A:=fun n=> show Cross L₀ a b from meshBook g e [] (P(n))) hs (fun p hc hP=>?_); exact issuing A i p hc g e h (he p hc hP)
lemma tower_fields : Sailing (fun n=> show Cross L₀ (TypeFace 1) (TypeFace 1) from (duo K (P(n))).A0) ∧ Sailing (fun n=> show Cross L₀ (TypeFace 2) (TypeFace 2) from (duo K (P(n))).T) ∧ Sailing fun n=> show Cross L₀ (TypeFace 2) (TypeFace 2) from buckle K (P(n)) := by
  have ht:=A.clock.adm (i+1); have hm:= A.clock.adm i
  obtain ⟨hA,hT⟩:= secure_both K hK ht hm
  refine ⟨frames_sail A i K hK _ hA 1 (fun p hc he l=> (duo_history A i K hK p hc he l).1),
    frames_sail A i K hK _ hT 2 (fun p hc he l=> (duo_history A i K hK p hc he l).2),?_⟩
  refine frames_sail A i K hK (agile K) (agility K hK ht hm) 2 (fun p hp hx l=>?_)
  have hr:= alias_base hp l (A.S.block_odd i)
  have he: aliasAt p l≠0:= (alias_regular (P:=P(0)) (base_subset_realCube zone_pos hp) l (Or.inr hx)).2
  exact matprod ((colors A K hK (i+1) (aliasAt p l) hr he).2) (duo_history A i K hK p hp hx l|>.2)
lemma hedges :
    Sailing (fun n=> pink K (P(n)).land) ∧ Sailing (fun n=> blue K (P(n)).land) ∧ Sailing (fun n=> blue K (P(n)).wing) := by
  have ht:=A.clock.adm (i+1); have hm:= A.clock.adm i
  have hh n (h:i<n) := loc_land A n i h
  obtain ⟨hA,hB⟩:= heart_saves K hK hm (fun (n:ℕ)=> (P(n)).land)
  refine ⟨Sailing.of_read hA (fun p hp hn=>?_), Sailing.of_read hB (fun p hp hn=>?_ ),
    Sailing.of_read ((heart_saves K hK ht (fun (n:ℕ)=> (P(n)).wing)).2) (fun p hp hn=>?_ )⟩
  · refine (colors A K hK i p hp hn|>.1).copy ?_; filter_upwards [eventually_gt_atTop i] with n h
    rw [hh n h]; exact ((heart_true K hK hm (P(n)).land).1.echo _ hp).symm
  · refine (colors A K hK i p hp hn|>.2).copy ?_; filter_upwards [eventually_gt_atTop i] with n h
    rw [hh n h]; exact ((heart_true K hK hm (P(n)).land).2.echo _ hp).symm
  exact (colors A K hK (i+1) p hp hn|>.2).copy (Eventually.of_forall fun n=> ((heart_true K hK ht (P(n)).wing).2.echo _ hp).symm)

lemma reel (q l : ℝ) (hl : 0 ≤ l) : Sailing fun n=> (P(n)).rollFunds K q l := by
  have ht:=A.clock.adm (i+1); have hm:= A.clock.adm i
  obtain ⟨hA,hB,hW⟩:= hedges A i K hK
  obtain ⟨h₁,h₂,h₃⟩:= tower_fields A i K hK
  let R n := (P(n)).land
  have h : Sailing fun n=> Flight.gap K (P(n)):=
    Sailing.minus (Sailing.minus hB (Sailing.mul (Sailing.transpose h₂) h₃))
      (Sailing.scalar (Sailing.mul (Sailing.const _ (Whole.boundary 1)) (Sailing.transpose (Sailing.const _ (Whole.boundary 1)))) _)
  have hp : Sailing fun n=> leftFunds K (P(n)):= Sailing.twice (Sailing.mul (Sailing.mul hA h) hA)
  have hx : Sailing fun n=> fund K (P(n)):= Sailing.scalar (Sailing.plus hp (Sailing.transpose hp)) _
  have hg : Sailing fun n=> show Cross L₀ (TypeFace 3) (TypeFace 2) from curlStep K (P(n)):= by
    constructor
    · obtain ⟨σ,C,hσ,hC,hP⟩:= (budget_curl K hK ht hm).uniform
      let t:= C* (((L₀).val:ℝ)^3)⁻¹; have hv : 0<t:= by unfold t; positivity
      refine ⟨fun _=> zero_le_one,σ,t,hσ,hv,fun q=> ?_⟩; rw [mul_one]; exact hP (P(q))
    refine from_installations ?_; intro c f hP
    exact (matR (Arrives.steady ((cobound 2).acts f)) (installations h₃ c f hP)).copy
      (Eventually.of_forall fun n=> (Whole.from_fine ⟨L₀,hP⟩ (Whole.boundary 2) (h₃.1.whole n)).symm)
  have hu:= Sailing.fold (r:=1) (Sailing.mul hg hA) (List.finRange 4)
  have hd:= Sailing.mul (Sailing.transpose hu) hu
  have hy:= Sailing.minus (Sailing.plus hx (Sailing.scalar (Sailing.const _ (Whole.coin _)) l)) (Sailing.scalar hd q)
  have hD : Sailing fun n=> bail K l (R n):=
    Sailing.plus (Sailing.const _ (Whole.coin _)) (Sailing.scalar (Sailing.mul
      (Sailing.mul (Sailing.const _ (Whole.boundary 2)) hB) (Sailing.transpose (Sailing.const _ (Whole.boundary 2)))) l)
  let H := fun n=> treble K l (R n)
  have he := insurance K l hK hl hm R |>.2
  obtain ⟨σ,C,hσ,hC,hP⟩:= he.stock.uniform
  have hv : ∀ᶠ i in atTop, (H i).strip σ C:= Eventually.of_forall fun i=> by simpa only [mul_one] using hP i
  obtain ⟨T,hT⟩:= inverse_row hσ hv hD.2 (Eventually.of_forall fun i p=> (heated (bail_warm K l hK hl hm R)|>.2 i).2 p)
  have hk: Sailing H:= ⟨he.stock,fun n=> ⟨_,acts_limit hT hv hσ _⟩⟩
  exact Sailing.mul (Sailing.mul (Sailing.transpose hk) hy) hk
end YM.UVExtension.Free
