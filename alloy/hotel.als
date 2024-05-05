module examples/hotel
open util/ordering [Time] as TO
open util/ordering [Key] as KO
sig Key {}
sig Time {}
sig Room {
  keys: set Key,
  currentKey: Key one -> Time
}
sig Guest {
  gkeys: Key -> Time
}
one sig FrontDesk {
 lastKey: (Room -> lone Key) -> Time,
 occupant: Room -> Guest -> Time
}


fact {
  -- Каждый ключ не больше одной комнаты
  all k: Key | lone keys.k
  all r:Room, t:Time | r.currentKey.t in r.keys 
}

-- Возвращает минимальный ключ из ks 
-- следующий после k
-- Нужен для обнаружения свободного ключа для 
-- новых посетителей
fun nextKey [k: Key, ks: set Key]: set Key
{
	KO/min [KO/nexts[k] & ks]
}

pred init [t: Time] {
	-- У всех гостей нет никаких ключей
	no Guest.gkeys.t
	-- На стене ключи никем не заняты
	no FrontDesk.occupant.t
	-- Все ключи в комнатах и на стене ресепшена
      -- синхронизированы
	all r: Room | 
	 r.(FrontDesk.lastKey.t) = r.currentKey.t
}

pred entry [ g: Guest, r: Room, k: Key, 
					 t, t1: Time ] {
	-- У гостя есть ключ от своей комнаты
	k in g.gkeys.t

	let ck = r.currentKey |
		-- если ключ остался тот же, то состояния
            -- в t1 и t одно и то же для ключа
            -- это равносильно гостю который уже был
		(k = ck.t and ck.t1 = ck.t) or 
		-- Иначе берём следующий наименьший ключ из
            -- всех в наборе и присваем его к данному ключу
            -- от комнаты 
		(k = nextKey [ck.t, r.keys] and ck.t1 = k)

      -- просто проверяем что в других комнатах
	noRoomChangeExcept [r, t, t1]
      -- для других гостей
	noGuestChangeExcept [none, t, t1]
      -- для стенки у ресепшена
	noFrontDeskChange [t, t1]
      -- ничего не поменялось
}

-- описываем проверку не изменения состояния
-- это используется в функция изменения состояния
-- для отслеживания стабильности изменений
pred noFrontDeskChange [t,t1: Time] 
{
      -- очевидно: просто проверяем что ничего не поменялось
	FrontDesk.lastKey.t = FrontDesk.lastKey.t1
	FrontDesk.occupant.t = FrontDesk.occupant.t1
}
-- мы должны сначала убрать из сета всех комнат
-- ту, которую мы изменяли
-- затем проверяем что ничего не поменялось
pred noRoomChangeExcept [rs: set Room, t,t1: Time]
{
	all r: Room - rs |
		r.currentKey.t = r.currentKey.t1
}
-- аналогично, только не рассматриваем текущего гостя
pred noGuestChangeExcept [gs: set Guest, t,t1: Time] 
{
	all g: Guest - gs | g.gkeys.t = g.gkeys.t1
}

pred checkout [ g: Guest, t,t1: Time ]
{
	let occ = FrontDesk.occupant | {
	  -- проверяем что гость занимал хотя бы
        -- одну комнату
	  some occ.t.g
	  -- в следующий момент времени освобождаем
        -- комнаты, занимаемые гостем
	  occ.t1 = occ.t - (Room -> g)
	}
	FrontDesk.lastKey.t = FrontDesk.lastKey.t1
	noRoomChangeExcept [none, t, t1]
	noGuestChangeExcept [none, t, t1]
}

pred checkin [ g: Guest, r: Room, k: Key, t,t1: Time ] {
	-- гостю даём ключ 
	g.gkeys.t1 = g.gkeys.t + k

	let occ = FrontDesk.occupant | {
		-- Проверяем что в выбранной комнате никто не живёт
		no r.occ.t
		-- Бронируем комнату (ключи уже отдали)
		occ.t1 = occ.t + r->g 
	}

	let lk = FrontDesk.lastKey | {
		-- продвигаем lastKey
		lk.t1 = lk.t ++ r->k
		-- проверяем что k - это следующий за lastKey
            -- кто используется
		k = nextKey [r.lk.t, r.keys]
	}
      -- просто опять проверки
	noRoomChangeExcept [none, t, t1]
	noGuestChangeExcept [g, t, t1]
}

-- Запуск одной из операций
-- Вызывем из Traces
pred trans[t,t1: Time] {
 some g: Guest, r: Room, k: Key |
   entry[g, r, k, t, t1] or
   checkin[g, r, k, t, t1] or
   checkout[g, t, t1]
}

fact Traces {
      -- проверяем что выполнены начальные условия
	init [TO/first]
	-- в каждый момент времени кроме последнего
      -- запускаем одну из операций
      all t: Time - TO/last | trans[t, TO/next [t]]
}

-- Упадёт если не проверять на пересечение пользователями
assert noBadEntry  {
	all t: Time, r: Room, g: Guest, k: Key | 
        let t1 = TO/next [t],
        -- o = тот, кем окупирована данная комната
        o = r.(FrontDesk.occupant).t |
            -- если o не пусто (кто-то используем комнату)
            -- и получилось войти, то обязательно в информации
            -- о том, что окупировал комнату этот гость будет
		(entry [g, r, k, t, t1] and some o)
			implies g in o
}

-- Не должно быть пересекающихся операций
-- Можете убрать, чтобы увидеть контрпример assert 
--   который падает и из-за которого приходится вводить
--   эту проверку
fact noIntervening {
  -- будем рассматривать сразу 3 последовательных
  -- момента времени
  all t: Time - TO/last |
    let t1 = TO/next [t] |
      let t2 = TO/next [t1] |
        all g: Guest, r: Room, k: Key |
          -- в момент t он заселяется
          checkin[g, r, k, t, t1] implies
          (
            -- а в следующий пытается войти к себе домой
            entry[g, r, k, t1, t2] or
            -- если entry не выполняется, то такого не
            -- может быть
            no t2
          )
}

check noBadEntry for 4
but 2 Room, 2 Guest, 5 Time
