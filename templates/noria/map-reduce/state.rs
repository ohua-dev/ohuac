use state::cstate::SpecialStateWrapper;

impl State for
    SpecialStateWrapper<
    // <begin(udf-state-type)>
    super::click_ana::ClickAnaState
    // <end(udf-state-type)>
    >
{

    fn add_key(&mut self, columns: &[usize], partial: Option<Vec<Tag>>) {
        self.0.add_key(columns, partial)
    }

    fn is_useful(&self) -> bool {
        self.0.is_useful()
    }

    fn is_partial(&self) -> bool {
        self.0.is_partial()
    }

    fn process_records(&mut self, records: &mut Records, partial_tag: Option<Tag>) {
        self.0.process_records(records, partial_tag)
    }

    fn mark_hole(&mut self, key: &[DataType], tag: Tag) {
        self.0.mark_hole(key, tag)
    }

    fn mark_filled(&mut self, key: Vec<DataType>, tag: Tag) {
        self.0.mark_filled(key, tag)
    }

    fn lookup<'a>(&'a self, columns: &[usize], key: &KeyType) -> LookupResult<'a> {
        self.0.lookup(columns, key)
    }

    fn rows(&self) -> usize {
        self.0.rows()
    }

    fn keys(&self) -> Vec<Vec<usize>> {
        self.0.keys()
    }

    fn cloned_records(&self) -> Vec<Vec<DataType>> {
        self.0.cloned_records()
    }

    fn evict_random_keys(&mut self, count: usize) -> (&[usize], Vec<Vec<DataType>>, u64) {
        self.0.evict_random_keys(count)
    }

    fn evict_keys(&mut self, tag: Tag, keys: &[Vec<DataType>]) -> Option<(&[usize], u64)> {
        self.0.evict_keys(tag, keys)
    }

    fn clear(&mut self) {
        self.0.clear()
    }

    // <insert(state-trait-coerce-impls)>
}
